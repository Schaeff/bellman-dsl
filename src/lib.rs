#![feature(box_syntax, box_patterns)]

extern crate bellman;
extern crate pairing;
extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::thread_rng;

// Bring in some tools for using pairing-friendly curves
use pairing::{Engine, Field, PrimeField};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use pairing::bls12_381::Bls12;

// We'll use these interfaces to construct our circuit.
use bellman::{Circuit, ConstraintSystem, LinearCombination, SynthesisError, Variable};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    create_random_proof, generate_random_parameters, prepare_verifying_key, verify_proof, Proof,
};

use std::collections::HashMap;

// data structure to hold a FieldElement variable with its value
// it's fine to clone these
#[derive(Clone)]
struct AssignedVariable<E: Engine> {
    variable: Variable,
    value: E::Fr,
}

// data structure to hold a Linear Combination of variables, with its value.
// it's also fine to clone these
#[derive(Clone)]
struct AssignedLinearCombination<E: Engine> {
    combination: LinearCombination<E>,
    value: E::Fr,
}

// an AssignedVariable can be turned into an AssignedLinearCombination
impl<E: Engine> From<AssignedVariable<E>> for AssignedLinearCombination<E> {
    fn from(assigned_variable: AssignedVariable<E>) -> Self {
        AssignedLinearCombination {
            combination: LinearCombination::zero() + assigned_variable.variable,
            value: assigned_variable.value,
        }
    }
}

// data structure to hold the binding between a typed DSL expression and its underlying
// representation in the constraint system, in the form of many AssignedLinearCombinations
#[derive(Clone)]
struct TypedBinding<E: Engine> {
    lcs: Vec<AssignedLinearCombination<E>>,
    _type: Type,
}

// convenience function to navigate between those data structures
impl<E: Engine> TypedBinding<E> {
    fn field_element<T: Into<AssignedLinearCombination<E>>>(lcs: Vec<T>) -> Self {
        TypedBinding {
            lcs: lcs.into_iter().map(|l| l.into()).collect(),
            _type: Type::FieldElement,
        }
    }
}

// the types we support: field elements, and arrays of field elements
// we do not enforce a static size on the array just yet
#[derive(Clone)]
enum Type {
    FieldElement,
    FeArray,
}

// a typed argument to a function, like: `a: field[]`
struct Argument {
    name: String,
    _type: Type,
}

impl Argument {
    pub fn field_element<S: Into<String>>(name: S) -> Self {
        Argument {
            name: name.into(),
            _type: Type::FieldElement,
        }
    }
}

// data structures for a program
// we don't want to clone these as they contain strings
struct Program<E: Engine> {
    main: Function<E>,
    functions: Vec<Function<E>>,
}

struct Function<E: Engine> {
    id: String,
    arguments: Vec<Argument>,
    statements: Vec<Statement<E>>,
}

enum Statement<E: Engine> {
    Definition(String, Expression<E>),
    Return(Expression<E>),
}

enum Expression<E: Engine> {
    FieldElement(FieldElementExpression<E>),
    FeArray(FeArrayExpression<E>),
}

impl<E: Engine> From<FieldElementExpression<E>> for Expression<E> {
    fn from(fe: FieldElementExpression<E>) -> Self {
        Expression::FieldElement(fe)
    }
}

impl<E: Engine> From<FeArrayExpression<E>> for Expression<E> {
    fn from(fea: FeArrayExpression<E>) -> Self {
        Expression::FeArray(fea)
    }
}

// a field element expression can be reduced in different ways
enum FieldElementExpression<E: Engine> {
    Number(E::Fr),
    Add(
        Box<FieldElementExpression<E>>,
        Box<FieldElementExpression<E>>,
    ),
    Identifier(String),
    FunctionCall(String, Vec<Expression<E>>), // no arguments, one return value
}

// an array must be a constant for now
enum FeArrayExpression<E: Engine> {
    Constant(Vec<E::Fr>),
}

impl<E: Engine> Expression<E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        context: &[Function<E>],
        symbols: &mut HashMap<String, TypedBinding<E>>,
    ) -> Result<TypedBinding<E>, SynthesisError> {
        match *self {
            Expression::FieldElement(ref e) => e.flatten(cs, context, symbols),
            Expression::FeArray(ref e) => e.flatten(cs),
        }
    }
}

impl<E: Engine> FieldElementExpression<E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        context: &[Function<E>],
        symbols: &mut HashMap<String, TypedBinding<E>>,
    ) -> Result<TypedBinding<E>, SynthesisError> {
        match *self {
            FieldElementExpression::Number(n) => {
                let var = cs.alloc(|| n.to_string(), || Ok(n))?;

                Ok(TypedBinding::field_element(vec![AssignedVariable {
                    variable: var,
                    value: n,
                }]))
            }
            FieldElementExpression::Identifier(ref id) => {
                let assigned_variable = symbols.get(id).ok_or(SynthesisError::AssignmentMissing)?;

                Ok((*assigned_variable).clone())
            }
            FieldElementExpression::FunctionCall(ref f_id, ref arguments) => {
                let fun = context
                    .iter()
                    .find(|f| &f.id == f_id)
                    .expect("undefined function");

                let mut inputs = vec![];
                for arg in arguments {
                    let assigned_variable = arg.flatten(cs, context, symbols)?;

                    inputs.push(assigned_variable);
                }

                let assigned_output = fun.flatten(cs, context, &inputs)?;

                Ok(assigned_output)
            }
            FieldElementExpression::Add(ref a, ref b) => {
                // naive approach: create a new wire for each term in the sum

                let assigned_variable_a = a.flatten(cs, context, symbols)?;

                let assigned_variable_b = b.flatten(cs, context, symbols)?;

                let assigned_variable_a = &assigned_variable_a.lcs[0];

                let assigned_variable_b = &assigned_variable_b.lcs[0];

                let mut res = assigned_variable_a.value;
                res.add_assign(&assigned_variable_b.value);

                let sum = cs.alloc(|| "sum", || Ok(res))?;

                // CONSTRAINT
                cs.enforce(
                    || "res = a + b",
                    |lc| lc + sum,
                    |lc| lc + CS::one(),
                    |lc| lc + &assigned_variable_a.combination + &assigned_variable_b.combination,
                );

                Ok(TypedBinding::field_element(vec![AssignedVariable {
                    variable: sum,
                    value: res,
                }]))
            }
        }
    }
}

impl<E: Engine> FeArrayExpression<E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
    ) -> Result<TypedBinding<E>, SynthesisError> {
        match *self {
            FeArrayExpression::Constant(ref values) => {
                let mut res = vec![];
                for v in values {
                    let var = cs.alloc(|| v.to_string(), || Ok(*v))?;
                    res.push(
                        AssignedVariable {
                            variable: var,
                            value: *v,
                        }.into(),
                    );
                }

                Ok(TypedBinding {
                    lcs: res,
                    _type: Type::FeArray,
                })
            }
        }
    }
}

impl<E: Engine> Statement<E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        context: &[Function<E>],
        symbols: &mut HashMap<String, TypedBinding<E>>,
        is_main: bool,
    ) -> Result<Option<TypedBinding<E>>, SynthesisError> {
        match *self {
            Statement::Definition(ref id, ref e) => {
                // condense right side into one wire with a value
                let binding = e.flatten(cs, context, symbols)?;

                // no need to create a new variable, just register `id` is worth e.flattened

                symbols.insert(id.clone(), binding);

                Ok(None)
            }
            Statement::Return(ref e) => {
                // condense right side into one wire with a value
                let binding = e.flatten(cs, context, symbols)?;

                let out = if is_main {
                    let mut res = vec![];
                    for c in binding.lcs {
                        // if we're in the main function, we need to make the return variable a public input in the CS
                        let out = cs.alloc_input(|| "out", || Ok(c.value))?;

                        // CONSTRAINT
                        cs.enforce(
                            || "out = e * ~one",
                            |lc| lc + &c.combination,
                            |lc| lc + CS::one(),
                            |lc| lc + out,
                        );
                        res.push(
                            AssignedVariable {
                                variable: out,
                                value: c.value,
                            }.into(),
                        )
                    }

                    TypedBinding {
                        lcs: res,
                        ..binding
                    }
                }
                // otherwise, we already have everything we need to return
                else {
                    binding
                };

                Ok(Some(out))
            }
        }
    }
}

impl<E: Engine> Function<E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        context: &[Function<E>],
        arguments: &[TypedBinding<E>],
    ) -> Result<TypedBinding<E>, SynthesisError> {
        let mut cs = &mut cs.namespace(|| self.id.to_string());

        // map from identifier to CS wire
        let mut symbols = HashMap::new();

        for (i, binding) in arguments.iter().enumerate() {
            let mut res = vec![];

            for c in &binding.lcs {
                let input = cs.alloc(|| format!("input {}", i), || Ok(c.value))?;

                cs.enforce(
                    || "arg = passed_arg",
                    |lc| lc + input,
                    |lc| lc + CS::one(),
                    |lc| lc + &c.combination,
                );

                res.push(
                    AssignedVariable {
                        variable: input,
                        value: c.value,
                    }.into(),
                );
            }

            symbols.insert(
                self.arguments[i].name.clone(),
                TypedBinding {
                    lcs: res,
                    ..binding.clone()
                },
            );
        }

        let is_main = self.id == "main";

        for statement in &self.statements {
            match statement.flatten(&mut cs, &context, &mut symbols, is_main) {
                Ok(Some(res)) => return Ok(res),
                Ok(None) => {}
                Err(e) => return Err(e),
            }
        }

        Err(SynthesisError::AssignmentMissing)
    }
}

impl<E: Engine> Circuit<E> for Program<E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        match self.main.flatten(cs, &self.functions, &[]) {
            Ok(..) => Ok(()),
            Err(e) => Err(e),
        }
    }
}

fn number_to_fr<E: Engine>(number: usize) -> E::Fr {
    E::Fr::from_str(&number.to_string()).unwrap()
}

#[test]
fn test_function_calls() {
    let rng = &mut thread_rng();

    // our toy program
    // def main():
    //    a = foo(3)
    //    return a + 42
    //
    // def foo(b):
    //    return b + 1
    //
    // should return 43
    let program = Program::<Bls12> {
        main: Function {
            id: "main".to_string(),
            arguments: vec![],
            statements: vec![
                Statement::Definition(
                    String::from("a"),
                    FieldElementExpression::FunctionCall(
                        "foo".to_string(),
                        vec![FieldElementExpression::Number(number_to_fr::<Bls12>(3)).into()],
                    ).into(),
                ),
                Statement::Return(
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier(String::from("a")),
                        box FieldElementExpression::Number(number_to_fr::<Bls12>(42)),
                    ).into(),
                ),
            ],
        },
        functions: vec![Function {
            id: "foo".to_string(),
            arguments: vec![Argument::field_element("b")],
            statements: vec![Statement::Return(
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier(String::from("b")),
                    box FieldElementExpression::Number(number_to_fr::<Bls12>(1)),
                ).into(),
            )],
        }],
    };

    println!("Creating parameters...");

    let params = generate_random_parameters(program, rng).unwrap();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_vec = vec![];

    // Create an instance of our circuit (pass inputs, they were not needed for the setup)
    let computation = Program::<Bls12> {
        main: Function {
            id: "main".to_string(),
            arguments: vec![],
            statements: vec![
                Statement::Definition(
                    String::from("a"),
                    FieldElementExpression::FunctionCall(
                        "foo".to_string(),
                        vec![FieldElementExpression::Number(number_to_fr::<Bls12>(3)).into()],
                    ).into(),
                ),
                Statement::Return(
                    FieldElementExpression::Add(
                        box FieldElementExpression::Identifier(String::from("a")),
                        box FieldElementExpression::Number(number_to_fr::<Bls12>(42)),
                    ).into(),
                ),
            ],
        },
        functions: vec![Function {
            id: "foo".to_string(),
            arguments: vec![Argument::field_element("b")],
            statements: vec![Statement::Return(
                FieldElementExpression::Add(
                    box FieldElementExpression::Identifier(String::from("b")),
                    box FieldElementExpression::Number(number_to_fr::<Bls12>(1)),
                ).into(),
            )],
        }],
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(verify_proof(&pvk, &proof, &[number_to_fr::<Bls12>(46)]).unwrap());
}

#[test]
fn test_types() {
    let rng = &mut thread_rng();

    // our toy program
    // def main():
    //    return (42, 43)
    //
    // should return (42, 43)
    let program = Program::<Bls12> {
        main: Function {
            id: "main".to_string(),
            arguments: vec![],
            statements: vec![Statement::Return(
                FeArrayExpression::Constant(vec![
                    number_to_fr::<Bls12>(42),
                    number_to_fr::<Bls12>(43),
                ]).into(),
            )],
        },
        functions: vec![],
    };

    println!("Creating parameters...");

    let params = generate_random_parameters(program, rng).unwrap();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_vec = vec![];

    // Create an instance of our circuit (pass inputs, they were not needed for the setup)
    let computation = Program::<Bls12> {
        main: Function {
            id: "main".to_string(),
            arguments: vec![],
            statements: vec![Statement::Return(
                FeArrayExpression::Constant(vec![
                    number_to_fr::<Bls12>(42),
                    number_to_fr::<Bls12>(43),
                ]).into(),
            )],
        },
        functions: vec![],
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(
        verify_proof(
            &pvk,
            &proof,
            &[number_to_fr::<Bls12>(42), number_to_fr::<Bls12>(43)]
        ).unwrap()
    );
}
