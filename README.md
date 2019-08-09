# A Mechanized Theory of Program Refinement

This site is the companion repository to the paper "A Mechanized Theory of Program Refinement".
This work uses Coq 8.8.1. To build the project, run the command *make -f CoqMakefile*

We recommand the installation of [Proof General](https://proofgeneral.github.io/) and [company coq](https://github.com/cpitclaudel/company-coq).

The source files are organized in two parts, the [theory](./src/theory) files and the [examples](./src/examples).

## Theory

The file [Statement.v](./src/theory/Statement.v) contains the formalization of the syntax of the language of
program designs described in Section 3.1 of the paper.

In [FloydHoareWp.v](./src/theory/FloydHoareWp.v) we define a Hoare-style semantics for the language of program designs.
The refinement relation is defined in terms of hoare triples. To be as close as possible to the classical Hoare
rules, our Hoare style semantics is limited to block free statements. Also, to simplify matters we have strived
for minimality, hence there is one rule per syntactic construct. As a consequence, one will not find in our
encoding some of the classical rules (e.g. the rule of consequence), however all the absent rules are derivable
from the rules we have encoded.

The encoding of the predicative semantics (Section 4 of the paper) can be found in [Predicative.v](./src/theory/Predicative.v).
This files also contains a definition of the refinement relation in terms of the predicative semantics, the
statements and proofs of the properties of the refinement relation (i.e. the fact that it is a preorder and
that the control structures are monotonic w.r.t. refinement), and the theorem providing a sound and complete
method to prove that a while statement refines a specification (Theorem 2 in the paper).

The proof of equivalence between the predicative and Hoare-style definitions of refinement canbe found
in [FloydHoareWp_Predicative.v](./src/theory/FloydHoareWp_Predicative.v). The equivalence is proved for
block free statements only since our Hoare-style semantics is restricted to such statements. In particular
this equivalence is used to prove that the use of logical constants is not necessary to properly define
refinement in terms of Hoare triples.

The calculus of weakest prespecifications used to compute proof obligations is formalized in [Wpr.v](src/theory/Wpr.v).
In this file, one will also find a definition of refinement in terms of the wpr specification transformer,
and a proof of equivalence between this definition and the predicative definition in [Predicative.v](./src/theory/Predicative.v).

The encoding of the design rules is in [CbC.v](./src/theory/CbC.v). The soundness and completeness of the
design rules (Theorem 1 in the paper) are proved in this file.

## Examples

The [examples](./src/examples) directory illustrate how our formalization can be used in program verification
and in program design. The files in the [pred](./src/examples/pred) and [wpr](./src/examples/wpr) directories
are examples of program verification using the predicative semantics or the weakest prespecification calculus.
The files in the [design](./src/examples/design) directory are examples of program designs. The whole program design presented in the paper can be found in [Sqrt.v](./src/examples/design/Sqrt.v).



