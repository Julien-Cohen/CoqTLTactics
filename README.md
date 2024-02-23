# Tactics for CoqTL

We provide here some support (essentially tactics) for users who have built a model transformation with CoqTL and who want to prove some properties on that transformation.

## CoqTL

CoqTL is an internal language in Coq, for writing rule-based model- and graph- transformations. 

## Organization of the repository 

* `core/` - The CoqTL transformation engine and language (modified).

* `usertools/` - Support for user proofs (lemmas and tactics, main contribution).

* `transformations/` - Sample CoqTL transformations and user proofs.
  * `Moore2Mealy/` - Moore / Mealy metamodels and transformation.
    * `theorems/` - Structural properties on the transformation, and proof of preservation of the semantics.
  * `Moore2MealyALT/` - A simpler version of Moore and Mealy metamodels, which results in simpler proofs (without use of links). 
  * `Class2Relational/` - Class / Relational metamodels and transformation.
    * `theorems/` - Structural properties proven on this transformation.
  * `Class2Relational_TUPLES` - variation of Class to Relational, with more complex patterns in rules.


## Installation

CoqTL requires a working installation of [Coq](https://coq.inria.fr/) (`coqc`) and Make (`make` and `coq_makefile`). It is tested under Coq 8.19.0.

To init the Makefile:
```
cd coqTLTactics
sh init.sh
```
## Usage
* Run `make proofs` to run the proofs of properties with our tactics on the two main examples of transformations (Moore2Mealy and Class2Relational), and their dependancies (in particular, the definition of the transformation engine).
* Run `make tactic_tests` to run some unit tests. 
* Run `make transformation_tests` to run the two main examples of transformations on examples of models and see the output. 
* Run `make` to build all the proofs, including proofs that are not in the previous targets.
* This builds :
  * Definitions for the transformation language and the transformation engine (adapted from previous work).
  * The lemmas (with their proofs) and tactics we provide for user support (this contribution).
  * Several definitions of metamodels.
  * Several definitions of transformations.
  * Several properties (with their proofs) of those transformations, some structural and some semantics.
  * Several examples of models that conform to the given metamodels. 
  * Several examples of application of the transformations run by the engine on those models.
  * Several properties (with their proofs) of the transformation engine, such as additivity which still hold after refactoring of the the engine (adapted from previous work).
* Run `make html` to build a navigable HTML version of the source code. HTML code is generated in the `html` directory.
* Each build takes less than a minute on a machine with 4 cores (make -j 4), less than 3 minutes in a virtual machine with 1 core.
* To run proofs interactively, open the file you want in your IDE (works with `coqide`, Emacs/ProofGeneral, and VSCode/VsCoq).

Try your own transformations: 
* To explore the construction of a model transformation, add your files in the `_CoqProject` file and run `./init.sh`, then `make`.
    
## Contributors and Previous Publications

The contributors of this work are **Julien Cohen** (Nantes Université, LS2N), **Massimo Tisi** (IMT Atlantique, LS2N) and **Rémi Douence** (IMT Atlantique, LS2N). Zheng Cheng provided some support to test the tactics. The core transformation engine has been adapted by the contributors to support the user tactics provided here, but this core transformation engine is a previous contribution, described in the following publications.  

* Massimo Tisi, Zheng Cheng. CoqTL: an Internal DSL for Model Transformation in Coq. ICMT'2018. [[pdf]](https://hal.inria.fr/hal-01828344/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Rémi Douence. CoqTL: A Coq DSL for Rule-Based Model Transformation. SOSYM'2019. [[pdf]](https://hal.archives-ouvertes.fr/hal-02333564/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Joachim Hotonnier. Certifying a Rule-Based Model Transformation Engine for Proof Preservation. MODELS'2020. [[pdf]](https://hal.inria.fr/hal-02907622/document) [[git]](https://github.com/atlanmod/CoqTL/tree/2a8cea5)
* Zheng Cheng, Massimo Tisi. Deep Specification and Proof Preservation for the CoqTL Transformation Language. [[git]](https://github.com/atlanmod/CoqTL/tree/948eb94)

## Questions and discussion

If you experience issues installing or using the provided tools, you can contact us at:

* Massimo Tisi: massimo.tisi@imt-atlantique.fr
* Julien Cohen: Julien.Cohen@univ-nantes.fr

## License

CoqTL itself is licensed under Eclipse Public License (v2). See LICENSE.md in the root directory for details. Third party libraries are under independent licenses, see their source files for details.
