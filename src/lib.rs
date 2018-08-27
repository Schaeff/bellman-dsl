#![feature(box_syntax, box_patterns)]

extern crate bellman;
extern crate pairing;
extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng};

// Bring in some tools for using pairing-friendly curves
use pairing::{
    Engine,
    Field,
    PrimeField,
};

// We're going to use the BLS12-381 pairing-friendly elliptic curve.
use pairing::bls12_381::{
    Bls12
};

// We'll use these interfaces to construct our circuit.
use bellman::{
    Circuit,
    ConstraintSystem,
    SynthesisError,
    Variable,
    LinearCombination,
};

// We're going to use the Groth16 proving system.
use bellman::groth16::{
    Proof,
    generate_random_parameters,
    prepare_verifying_key,
    create_random_proof,
    verify_proof,
};


use std::collections::{HashMap};

// data structure to hold a FieldElement variable with its value
// it's fine to clone these
#[derive(Clone)]
struct AssignedVariable<E: Engine> {
	variable: Variable,
	value: E::Fr
}

#[derive(Clone)]
struct AssignedLinearCombination<E: Engine> {
	combination: LinearCombination<E>,
	value: E::Fr
}

impl<E: Engine> From<AssignedVariable<E>> for AssignedLinearCombination<E> {
	fn from(assigned_variable: AssignedVariable<E>) -> Self {
		AssignedLinearCombination {
			combination: LinearCombination::zero() + assigned_variable.variable,
			value: assigned_variable.value
		}
	}
}

// data structures for a program
// we don't want to clone these as they contain strings
struct Program<E: Engine> {
	main: Function<E>,
	functions: Vec<Function<E>>
}

struct Function<E: Engine> {
	id: String,
	arguments: Vec<String>,
	statements: Vec<Statement<E>>,
}

enum Statement<E: Engine> {
	Definition(String, Expression<E>),
	Return(Expression<E>)
}

enum Expression<E: Engine> {
	Number(E::Fr),
	Add(Box<Expression<E>>, Box<Expression<E>>),
	Identifier(String),
	FunctionCall(String, Vec<Expression<E>>) // no arguments, one return value
}

impl<E: Engine> Expression<E> {
	fn flatten<CS: ConstraintSystem<E>>(
		&self,
		cs: &mut CS,
		context: &Vec<Function<E>>,
		symbols: &mut HashMap<String, AssignedLinearCombination<E>>
	) -> Result<AssignedLinearCombination<E>, SynthesisError>
	{
		match *self {
			Expression::Number(n) => {
				let var = cs.alloc(|| n.to_string(), || {
					Ok(n)
				})?;

				Ok(AssignedVariable { variable: var, value: n }.into())
			},
			Expression::Identifier(ref id) => {
				let assigned_variable = symbols.get(id).ok_or(SynthesisError::AssignmentMissing)?;

				Ok((*assigned_variable).clone())
			},
			Expression::FunctionCall(ref f_id, ref arguments) => {

				let fun = context.iter().find(|f| &f.id == f_id).expect("undefined function");

				let mut inputs = vec![];
				for arg in arguments {
					let assigned_variable = arg.flatten(
						cs,
						context,
						symbols
					)?;

					inputs.push(assigned_variable);
				}		

				let assigned_output = fun.flatten(
					cs,
					context,
					&inputs,
				)?;

				Ok(assigned_output)
			},
			Expression::Add(ref a, ref b) => {
				// naive approach: create a new wire for each term in the sum

				let assigned_variable_a = a.flatten(
					cs, 
					context,
					symbols
				)?;

				let assigned_variable_b = b.flatten(
					cs, 
					context,
					symbols,
				)?;

				let mut res = assigned_variable_a.value;
				res.add_assign(&assigned_variable_b.value);

				let sum = cs.alloc(|| format!("sum"), || {
					Ok(res)
				})?;

				// CONSTRAINT
				cs.enforce(
	                || "res = a + b",
	                |lc| lc + sum,
	                |lc| lc + CS::one(),
	                |lc| lc + &assigned_variable_a.combination + &assigned_variable_b.combination
	            );

	            Ok(AssignedVariable { variable: sum, value: res }.into())
			}
		}
	}
}

impl<E: Engine> Statement<E> {
	fn flatten<CS: ConstraintSystem<E>>(
		&self, 
		cs: &mut CS,
		context: &Vec<Function<E>>,
		symbols: &mut HashMap<String, AssignedLinearCombination<E>>,
		is_main: bool,
	) -> Result<Option<AssignedLinearCombination<E>>, SynthesisError>
	{
		match *self {
			Statement::Definition(ref id, ref e) => {
				// condense right side into one wire with a value
				let assigned_variable = e.flatten(
					cs,
					context,
					symbols
				)?;

				// no need to create a new variable, just register `id`is being worth e.flattened

	            symbols.insert(id.clone(), assigned_variable);

	            Ok(None)
			},
			Statement::Return(ref e) => {
				// condense right side into one wire with a value
				let assigned_variable = e.flatten(
					cs,
					context,
					symbols
				)?;

				let out = match is_main {
					// if we're in the main function, we need to make the return variable a public input in the CS
					true => {
						let out = cs.alloc_input(|| "out", || {
							Ok(assigned_variable.value)
						})?;

						// CONSTRAINT
						cs.enforce(
			                || "out = e * ~one",
			                |lc| lc + &assigned_variable.combination,
			                |lc| lc + CS::one(),
			                |lc| lc + out
			            );

			            AssignedVariable { variable: out, value: assigned_variable.value}.into()
					},
					// otherwise, we already have everything we need to return
					false => {
						assigned_variable
					}
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
		context: &Vec<Function<E>>,
		arguments: &Vec<AssignedLinearCombination<E>>,
	) -> Result<AssignedLinearCombination<E>, SynthesisError> 
	{
		let mut cs = &mut cs.namespace(|| format!("{}", self.id));

		// map from identifier to CS wire
		let mut symbols = HashMap::new();

		for (i, assigned_combination) in arguments.iter().enumerate() {
			symbols.insert(self.arguments[i].clone(), (*assigned_combination).clone());

			let input = cs.alloc(|| format!("input {}", i), || {
				Ok(assigned_combination.value)
			})?;

			cs.enforce(
				|| "arg = passed_arg",
				|lc| lc + input, 
				|lc| lc + CS::one(),
				|lc| lc + &assigned_combination.combination,
			);
		}

		let is_main = self.id == "main";

		for statement in self.statements.iter() {
			match statement.flatten(&mut cs, &context, &mut symbols, is_main) {
				Ok(Some(res)) => return Ok(res),
				Ok(None) => {},
				Err(e) => return Err(e)
			}
		}

		Err(SynthesisError::AssignmentMissing)
	}
}

impl<E: Engine> Circuit<E> for Program<E> { 
    fn synthesize<CS: ConstraintSystem<E>>(
        self,
        cs: &mut CS
    ) -> Result<(), SynthesisError>
    {
        match self.main.flatten(cs, &self.functions, &vec![]) {
        	Ok(..) => Ok(()),
        	Err(e) => Err(e)
        }
    }
}

fn number_to_fr<E: Engine>(number: usize) -> E::Fr {
	E::Fr::from_str(&number.to_string()).unwrap()
}

#[test]
fn test_program() {
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
				Statement::Definition(String::from("a"), Expression::FunctionCall("foo".to_string(), vec![Expression::Number(number_to_fr::<Bls12>(3))])),
				Statement::Return(
					Expression::Add(box Expression::Identifier(String::from("a")), box Expression::Number(number_to_fr::<Bls12>(42)))
				)
			]
		},
		functions: vec![
			Function {
				id: "foo".to_string(),
				arguments: vec!["b".to_string()],
				statements: vec![
					Statement::Return(
						Expression::Add(box Expression::Identifier(String::from("b")), box Expression::Number(number_to_fr::<Bls12>(1)))
					)
				]
			}
		]
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
				Statement::Definition(String::from("a"), Expression::FunctionCall("foo".to_string(), vec![Expression::Number(number_to_fr::<Bls12>(3))])),
				Statement::Return(
					Expression::Add(box Expression::Identifier(String::from("a")), box Expression::Number(number_to_fr::<Bls12>(42)))
				)
			]
		},
		functions: vec![
			Function {
				id: "foo".to_string(),
				arguments: vec!["b".to_string()],
				statements: vec![
					Statement::Return(
						Expression::Add(box Expression::Identifier(String::from("b")), box Expression::Number(number_to_fr::<Bls12>(1)))
					)
				]
			}
		]
    };

    // Create a groth16 proof with our parameters.
    let proof = create_random_proof(computation, &params, rng).unwrap();

    proof.write(&mut proof_vec).unwrap();

    let proof = Proof::read(&proof_vec[..]).unwrap();

    // Check the proof
    assert!(verify_proof(
        &pvk,
        &proof,
        &[number_to_fr::<Bls12>(46)]
    ).unwrap());
}
