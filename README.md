# Tactics for CoqTL

We provide here some support (essentially tactics) for user who have built a model transformation with CoqTL and who want to prove some properties on that transformation.

## CoqTL

CoqTL is an internal language in Coq, for writing rule-based model- and graph- transformations. 

## Organization of the repository 

* `core/` - The CoqTL transformation engine and language (modified).
  * `properties/` - Properties still proven on the modified core engine. 
* `usertools/` - Support for user proofs (lemmas and tactics, main contribution).
* `transformations/` - Sample CoqTL transformations and user proofs.
  * `Moore2Mealy/` - Moore / Mealy metamodels and transformation.
    * `theorems/` - Structural properties on the transformation, and proof of preservation of the semantics.
  * `Moore2MealyALT/` - A simpler version of Moore and Mealy metamodels, which results in simpler proofs (without use of links). 
  * `Class2Relational/` - Class / Relational metamodels and transformation.
    * `theorems/` - Structural properties proved on this transformation.
  * `Class2RelationalTUPLES` - variation of Class to Relational, with more complex patterns in rules.
* `libs/` - an importer that translates ECore metamodels into Coq. (The sources of the importer are in the [coqtl-model-import](https://github.com/atlanmod/coqtl-model-import) repository.)


## Installation

CoqTL requires a working installation of [Coq](https://coq.inria.fr/) (`coqc`) and Make (`make` and `coq_makefile`). It is tested under Coq 8.17.0 and 8.18.0.

To install CoqTL:
```
cd coqTL
./compile.sh
```
## Usage
* Run `./compile.sh` to build all the proofs. It takes less than a minute on a machine with 4 cores, less than 3 minutes in a vritual machine with 1 core. The build include :
  * Definitions for the transformation language and the transformation engine (former contribution).
  * Proofs of some properties of the transformation engine (former contribution).
  * Proofs and tactics for user support (this contribution).
  * Several metamodels definitions.
  * Several transformation definitions.
  * Several proofs of properties of those transformations, both structural and semantic.
  * Several models instances of the given metamodels. 
  * Several examples of transformations computed by the engine on those models.
* Run `make html` to build a navigable HTML version of the source code. HTML code is generated in the `html` directory.
* To run proofs interactively, open the file you want in your IDE (works with `coqide` without any additional configuration, also works with Emacs/ProofGeneral and VSCode/VsCoq).

Try your own transformations: 
* If you have an ECore file mymetamodel.ecore you want to translate into a CoqTL metamodel, run `make mymetamodel.v` . (That generator is not a contribution of this work.)
* To explore the construction of a model transformation, add your files in the `_CoqProject` file and run `./compile.sh`.
    
## Contributors and Previous Publications

The contributors of this work are **Julien Cohen** (Nantes Université, LS2N), **Massimo Tisi** (IMT Atlantique, LS2N) and **Rémi Douence** (IMT Atlantique, LS2N). Zheng Cheng provided some support to test the tactics. The core transformation engine has been adapted by the contributors to support the user tactics provided here, but this core transformation engine is a previous contribution, described in the following publications.  

* Massimo Tisi, Zheng Cheng. CoqTL: an Internal DSL for Model Transformation in Coq. ICMT'2018. [[pdf]](https://hal.inria.fr/hal-01828344/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Rémi Douence. CoqTL: A Coq DSL for Rule-Based Model Transformation. SOSYM'2019. [[pdf]](https://hal.archives-ouvertes.fr/hal-02333564/document) [[git]](https://github.com/atlanmod/CoqTL/tree/eee344e)
* Zheng Cheng, Massimo Tisi, Joachim Hotonnier. Certifying a Rule-Based Model Transformation Engine for Proof Preservation. MODELS'2020. [[pdf]](https://hal.inria.fr/hal-02907622/document) [[git]](https://github.com/atlanmod/CoqTL/tree/2a8cea5)
* Zheng Cheng, Massimo Tisi. Deep Specification and Proof Preservation for the CoqTL Transformation Language. [[git]](https://github.com/atlanmod/CoqTL/tree/948eb94)

## Questions and discussion

If you experience issues installing or using the provided tools, you can submit an issue on [github](https://github.com/atlanmod/coqtl/issues) or contact us at:

* Massimo Tisi: massimo.tisi@imt-atlantique.fr
* Julien Cohen: Julien.Cohen@univ-nantes.fr

## License

CoqTL itself is licensed under Eclipse Public License (v2). See LICENSE.md in the root directory for details. Third party libraries are under independent licenses, see their source files for details.
