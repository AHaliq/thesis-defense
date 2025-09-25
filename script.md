1.1

AS

- An accumulation scheme guarantees instances satisfy some predicate
- We can append new instances to get a single proof via accumulation
- Verify checks that the accumulation comes from a valid previous accumulation

VFast

- In our case, instances are plonk proofs, and predicate is proof is valid
- In plonk verification, we do a PC check, but this is offloaded to the AS decide run by the light node

Fq Fp

- We have the above in over two fields to express cycle of curves; pasta curves
- To express operations in AS and PlonkVer as a circuit
- Note a circuit has multiple types, we verify for each

IVC

- Is the above and payload function F over state s_i
- Above as secure compute guarantee of F

Schnorr

- F is chain of signatures, using a schnorr signature scheme
- instead of a chain of blocks, we have a chain of public keys of the commitee signing off blocks

visual

- and thats light node catchup at a high level
- we arithmetize this program as a circuit
- a light node then runs the AS decide on the current accumulation to verify the whole chain

  1.2

Plonk

- SNARK; witness PI; example
- at a high level
- plonk has many components - gate constraint polynomial, takes row as arg and if eval to zero holds - vanishing argument does this zero check - copy constraints check that connected wires when permutated are "equal" - grand product argument computes polynomials F1,F2 that on zero checks this - batched evaluation proof guarantees that the evaluations passed to verifier comes from the valid polynomial

  1.3

Motivation

- To prepare the polynomials used by the above, we arithmetize
- viability
- features

  2.1

Pipeline

- arithmetize is a sequence of algorithms
- build computes a program to an abstract circuit
- trace populates a table of values
- interpolate computes the root of unity and interpolates the columns into polynomials

  2.2 - as is

  2.3

Abs - We operate over 3 levels of abstractions, values, wires, and templates / properads

IMap - Very expressive and usable for many other more concrete abstractions

2.4

Trace - is a repeated application of a composition of 3 (monotone) functions

2.5 - as is

2.6 - as is

3.1 - as is
