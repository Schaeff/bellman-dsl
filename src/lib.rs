extern crate bellman;
extern crate pairing;
extern crate rand;

// For randomness (during paramgen and proof generation)
use rand::{thread_rng};

// Bring in some tools for using pairing-friendly curves
use pairing::{
    Engine,
    Field
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

struct Program<E: Engine> {
	main: Function<E>,
	functions: Vec<Function<E>>
}

#[derive(Clone)]
struct Function<E: Engine> {
	id: String,
	statements: Vec<Statement<E>>
}

#[derive(Clone)]
enum Statement<E: Engine> {
	Definition(String, Expression<E>),
	Return(Expression<E>)
}

#[derive(Clone)]
enum Expression<E: Engine> {
	Number(E::Fr),
	Identifier(String),
	FunctionCall(String) // no arguments, one return value
}

impl<E: Engine> Function<E> {
	fn synthesize_with_context<CS: ConstraintSystem<E>>(
		self,
		cs: &mut CS,
		context: &mut Vec<Function<E>>
	) -> Result<(Variable, E::Fr), SynthesisError> 
	{
		let mut cs = &mut cs.namespace(|| format!("{}", self.id));

		// map from identifier to CS wire
		let mut symbols = HashMap::new();
		// map from identifier to value 
		let mut witness = HashMap::new();

		for statement in self.statements.clone() {
			match statement {
				Statement::Definition(id, e) => {
					match e {
						Expression::Number(n) => {
							// SOLVER

							// store the value of the identifier in the witness
							witness.insert(id.clone(), n); // doing the same thing as cs.alloc?

							let var = cs.alloc(|| id.clone(), || {
								Ok(n) // should just be getting it from the witness?
							})?;

							// store the CS element against the name for future reference
				            symbols.insert(id, var);

							// CONSTRAINT
							cs.enforce(
				                || "id = n * ~one",
				                |lc| lc + (n, CS::one()),
				                |lc| lc + CS::one(),
				                |lc| lc + var
				            );
						},
						Expression::FunctionCall(f_id) => {
							// SOLVER
							// find the wires for the called function's return value

							let fun = context.iter().find(|f| f.id == f_id).expect("undefined function").clone();

							let (output_wire, output_val) = fun.clone().synthesize_with_context(
								&mut cs,
								context
							)?;

							// store the value of the identifier in the witness
							witness.insert(id.clone(), output_val); // doing the same thing as cs.alloc?

							let var = cs.alloc(|| id.clone(), || {
								Ok(output_val) // should just be getting it from the witness?
							})?;

							// store the CS element against the name for future reference
				            symbols.insert(id, output_wire);

							// CONSTRAINT
							cs.enforce(
				                || "id = f()",
				                |lc| lc + output_wire,
				                |lc| lc + CS::one(),
				                |lc| lc + var
				            );
						},
						_ => unimplemented!()
					}
				},
				Statement::Return(e) => {
					match e {
						Expression::Number(n) => {
							// SOLVER
							let out = match &self.id == "main" {
								// if we're in the main function, we need to make the return variable a public input in the CS
								true => {
									cs.alloc_input(|| "out", || {
										Ok(n)
									})
								},
								false => {
									cs.alloc(|| "out", || {
										Ok(n)
									})
								}
							}?;

							// CONSTRAINT
							cs.enforce(
				                || "out = n * ~one",
				                |lc| lc + (n, CS::one()),
				                |lc| lc + CS::one(),
				                |lc| lc + out
				            );

				            // export to Abi for this function to enable calling it!
				            context.push(self.clone());
				            return Ok((out, n));
						},
						Expression::Identifier(id) => {
							// SOLVER
							// find the CS variable for that id
							let var = symbols.get(&id).expect("semantic error, variable should be defined");
							let value = witness.get(&id).ok_or(SynthesisError::AssignmentMissing)?;

							let out = match &self.id == "main" {
								// if we're in the main function, we need to make the return variable a public input in the CS
								true => {
									cs.alloc_input(|| "out", || {
										Ok(*value)
									})
								},
								false => {
									cs.alloc(|| "out", || {
										Ok(*value)
									})
								}
							}?;

							// CONSTRAINT
							cs.enforce(
				                || "out = id",
				                |lc| lc + *var,
				                |lc| lc + CS::one(),
				                |lc| lc + out
				            );

				       		// export to Abi for this function to enable calling it!
				            context.push(self.clone()); // we don't cache yet so we'll have to flattened from scratch
				            return Ok((out, *value));
						},
						_ => unimplemented!()
					}
				}
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
    	let mut context = vec![];
    	let res: Vec<_> = self.functions.into_iter().map(|f| f.synthesize_with_context(cs, &mut context)).collect();
        match self.main.synthesize_with_context(cs, &mut context) {
        	Ok(..) => Ok(()),
        	Err(e) => Err(e)
        }
    }
}

#[test]
fn test_program() {
    let rng = &mut thread_rng();

    // our toy program
    // def main():
    //    a = foo()
    //    return a
    //
    // def foo():
    //    return 1
    let program = Program::<Bls12> {
		main: Function {
			id: "main".to_string(),
			statements: vec![
				Statement::Definition(String::from("a"), Expression::FunctionCall("foo".to_string())),
				Statement::Return(
					Expression::Identifier(String::from("a"))
				)
			]
		},
		functions: vec![
			Function {
				id: "foo".to_string(),
				statements: vec![
					Statement::Return(
						Expression::Number(<Bls12 as Engine>::Fr::one())
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
			statements: vec![
				Statement::Definition(String::from("a"), Expression::FunctionCall("foo".to_string())),
				Statement::Return(
					Expression::Identifier(String::from("a"))
				)
			]
		},
		functions: vec![
			Function {
				id: "foo".to_string(),
				statements: vec![
					Statement::Return(
						Expression::Number(<Bls12 as Engine>::Fr::one())
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
        &[<Bls12 as Engine>::Fr::one()]
    ).unwrap());
}
