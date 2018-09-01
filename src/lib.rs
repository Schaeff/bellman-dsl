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

// data structures for a program
// we don't want to clone these as they contain strings
struct Program<'a, E: Engine> {
    main: &'a Function<'a, E>,
}

struct Function<'a, E: Engine> {
    id: String,
    arguments: Vec<String>,
    statements: Vec<Statement<'a, E>>,
    return_variables: Vec<String>
}

enum Solver {
    Three,
    PlusOne,
}

impl Solver {
    fn execute<E: Engine>(&self, args: &[E::Fr]) -> Vec<E::Fr> {
        match *self {
            Solver::Three => vec![number_to_fr::<E>(3)],
            Solver::PlusOne => {
                let mut res = args[0];
                res.add_assign(&number_to_fr::<E>(1));
                vec![res]
            }
        }
    }
}

enum Statement<'a, E: Engine> {
    // constrain a relationship between some variables
    Constraint(
        Vec<(E::Fr, String)>,
        Vec<(E::Fr, String)>,
        Vec<(E::Fr, String)>,
    ),
    // set some new variables to some values
    Directive(Vec<String>, Vec<String>, Solver),
    // call a function and assign the results to some new variables
    Definition(Vec<String>, FunctionCall<'a, E>),
}

struct FunctionCall<'a, E: Engine>(&'a Function<'a, E>, Vec<String>);

impl<'a, E: Engine> Statement<'a, E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        symbols: &mut HashMap<String, AssignedVariable<E>>,
    ) -> Result<(), SynthesisError> {
        match *self {
            Statement::Definition(ref output_names, FunctionCall(ref fun, ref input_names)) => {
                let mut inputs = vec![];
                for name in input_names {
                    let assigned_variable = symbols.get(name).unwrap();

                    inputs.push(assigned_variable.clone());
                }

                let assigned_outputs = fun.flatten(cs, &inputs)?;

                // no need to create a new variable, just register `id` is worth e.flattened
                for (index, assignment) in assigned_outputs.iter().enumerate() {
                    symbols.insert(output_names[index].clone(), assignment.clone());
                }
            }
            Statement::Directive(ref var_names, ref arguments, ref solver) => {
                // get argument values
                let argument_values = &arguments
                    .iter()
                    .map(|a| symbols.get(a).unwrap().value)
                    .collect::<Vec<_>>();

                // apply solver to find result
                let res = solver.execute::<E>(&argument_values);

                for (index, r) in res.iter().enumerate() {
                    let var = cs.alloc(|| "directive result", || Ok(*r))?;
                    symbols.insert(
                        var_names[index].clone(),
                        AssignedVariable {
                            variable: var,
                            value: *r,
                        },
                    );
                }
            }
            Statement::Constraint(ref a, ref b, ref c) => {
                let a_comb = a
                    .iter()
                    .map(|(mult, var)| (*mult, symbols.get(var).unwrap().variable))
                    .fold(LinearCombination::zero(), |acc, term| acc + term);
                let b_comb = b
                    .iter()
                    .map(|(mult, var)| (*mult, symbols.get(var).unwrap().variable))
                    .fold(LinearCombination::zero(), |acc, term| acc + term);
                let c_comb = c
                    .iter()
                    .map(|(mult, var)| (*mult, symbols.get(var).unwrap().variable))
                    .fold(LinearCombination::zero(), |acc, term| acc + term);

                cs.enforce(
                    || "inline constraint",
                    |lc| lc + &a_comb,
                    |lc| lc + &b_comb,
                    |lc| lc + &c_comb,
                );
            }
        }
        Ok(())
    }
}

impl<'a, E: Engine> Function<'a, E> {
    fn flatten<CS: ConstraintSystem<E>>(
        &self,
        cs: &mut CS,
        arguments: &[AssignedVariable<E>],
    ) -> Result<Vec<AssignedVariable<E>>, SynthesisError> {
        let mut cs = &mut cs.namespace(|| self.id.to_string());

        // map from identifier to CS wire
        let mut symbols = HashMap::new();

        symbols.insert(
            "~one".to_string(),
            AssignedVariable {
                variable: CS::one(),
                value: number_to_fr::<E>(1),
            },
        );

        for (i, assignment) in arguments.iter().enumerate() {
            symbols.insert(self.arguments[i].clone(), assignment.clone());
        }

        let is_main = self.id == "main";

        for statement in &self.statements {
            statement.flatten(&mut cs, &mut symbols)?;
        }

        let assignments: Vec<AssignedVariable<E>> =
            self.return_variables.iter().map(|e| symbols.get(e).unwrap().clone()).collect();

        let out = if is_main {
            assignments
                .iter()
                .map(|a| {
                    // if we're in the main function, we need to make the return variable a public input in the CS
                    let out = cs.alloc_input(|| "out", || Ok(a.value)).unwrap();

                    // CONSTRAINT
                    cs.enforce(
                        || "out = e * ~one",
                        |lc| lc + a.variable,
                        |lc| lc + CS::one(),
                        |lc| lc + out,
                    );

                    AssignedVariable {
                        variable: out,
                        value: a.value,
                    }
                }).collect()
        }
        // otherwise, we already have everything we need to return
        else {
            assignments
        };

        Ok(out)
    }
}

impl<'a, E: Engine> Circuit<E> for Program<'a, E> {
    fn synthesize<CS: ConstraintSystem<E>>(self, cs: &mut CS) -> Result<(), SynthesisError> {
        match self.main.flatten(cs, &[]) {
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
    //	  # x = 3
    //	  x == 3
    //    a = foo(x)
    //    return a
    //
    // def foo(b):
    //	  # c = b + 1
    //	  c == b + 1
    //    return c
    //
    // should return 43

    let foo = Function {
        id: "foo".to_string(),
        arguments: vec!["b".to_string()],
        return_variables: vec!["c".to_string()],
        statements: vec![
            Statement::Directive(
                vec![String::from("c")],
                vec!["b".to_string()],
                Solver::PlusOne,
            ),
            Statement::Constraint(
                vec![(number_to_fr::<Bls12>(1), "c".to_string())],
                vec![(number_to_fr::<Bls12>(1), "~one".to_string())],
                vec![
                    (number_to_fr::<Bls12>(1), "b".to_string()),
                    (number_to_fr::<Bls12>(1), "~one".to_string()),
                ],
            ),
        ],
    };

    let main = Function {
        id: "main".to_string(),
        arguments: vec![],
        return_variables: vec!["a".to_string()],
        statements: vec![
            Statement::Directive(vec![String::from("x")], vec![], Solver::Three),
            Statement::Constraint(
                vec![(number_to_fr::<Bls12>(1), "x".to_string())],
                vec![(number_to_fr::<Bls12>(1), "~one".to_string())],
                vec![(number_to_fr::<Bls12>(3), "~one".to_string())],
            ),
            Statement::Definition(
                vec![String::from("a")],
                FunctionCall(&foo, vec!["x".to_string()]),
            ),
        ],
    };

    let program = Program::<Bls12> { main: &main };

    println!("Creating parameters...");

    let params = generate_random_parameters(program, rng).unwrap();

    // Prepare the verification key (for proof verification)
    let pvk = prepare_verifying_key(&params.vk);

    println!("Creating proofs...");

    let mut proof_vec = vec![];

    // Create an instance of our circuit (pass inputs, they were not needed for the setup)
    let computation = Program::<Bls12> { main: &main };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(verify_proof(&pvk, &proof, &[number_to_fr::<Bls12>(4)]).unwrap());
}
