from pyecore.resources import ResourceSet, URI
import os
import sys

def br():
    return "\n"

def join(lst):
    return br().join(lst)

def arg(name):
    return name.lower()

def map_eType(eType):
    tp = eType.name
    if tp == "EInt":
        return "nat"
    elif tp == "EBoolean":
        return "bool"
    elif tp == "EString":
        return "string"
    else:
        return "unknown_type"

def write(path, str):
    if os.path.isfile(path):
        new_path = path + '.bak'
        os.replace(path, new_path)

    with open(path, 'w+') as file:
        file.write(str)

def imports_native():
    '''
    Contract: Import native Coq libraries:
    * String
    * Bool
    * List
    * PeanoNat
    * EqNat
    * Coq.Logic.Eqdep_dec
    '''
    
    lst = []
    lst.append("(** Imports Native *)")
    lst.append("Require Import String.")
    lst.append("Require Import Bool.")
    lst.append("Require Import List.")    
    lst.append("Require Import PeanoNat.")
    lst.append("Require Import EqNat.")
    lst.append("Require Import Coq.Logic.Eqdep_dec.") 
    lst.append(br())

    return join(lst)

def imports_coqtl():
    '''
    Contract: Import CoqTL libraries:
    * core.utils.Utils for CoqTL utilities
    * core.Metamodel
    * core.modeling.ModelingMetamodel
    * core.Model
    * core.utils.CpdtTactics
    * core.Tactics
    '''
        
    lst = []  
    lst.append("(** Imports CoqTL *)")
    lst.append("Require Import core.utils.Utils.")
    lst.append("Require Import core.Metamodel.")
    lst.append("Require Import core.modeling.ModelingMetamodel.")
    lst.append("Require Import core.Model.")
    lst.append("Require Import core.utils.CpdtTactics.")
    lst.append("Require        core.Tactics.")
    lst.append(br())

    return join(lst)

def records_elem(eClasses):
    lst = []  
    lst.append("(** Base types for elements *)")

    for eClass in eClasses:
        records_elem_attr = lambda eAttribute : (f"{eClass.name}_{eAttribute.name} : {map_eType(eAttribute.eType)}")
        records_elem_attrs = " ; ".join(map(records_elem_attr, eClass.eAttributes))
        lst.append(f"Record {eClass.name}_t := {{ {records_elem_attrs} }}.")
        lst.append(f"Scheme Equality for {eClass.name}_t.")
        lst.append(f"Lemma lem_{eClass.name}_t_beq_id : forall (e1 e2 : {eClass.name}_t), {eClass.name}_t_beq e1 e2 = true -> e1 = e2.")
        lst.append("Proof. Admitted. ")
        lst.append(f"Lemma lem_{eClass.name}_t_beq_refl : forall (e : {eClass.name}_t), {eClass.name}_t_beq e e = true.")
        lst.append("Proof. Admitted. ")
    lst.append(br())

    return join(lst)

def records_link_multiplicity(eReference):
    if eReference.upperBound == 1:
        return eReference.eType.name
    else:
        return f"list {eReference.eType.name}"

def records_link_scheme_equality_list(eClass, eReference):
    lst = []
    lst.append(f"Definition {eClass.name}{eReference.name}_t_beq (a1 a2: {eClass.name}{eReference.name}_t) : bool := ") 
    lst.append(f"  {eClass.name}_t_beq a1.({eClass.name}{eReference.name}_t_source) a2.({eClass.name}{eReference.name}_t_source) && list_beq {eReference.eType.name}_t_beq a1.({eClass.name}{eReference.name}_t_target) a2.({eClass.name}{eReference.name}_t_target).")
    return join(lst)

def records_link(eClasses):
    lst = []  
    lst.append("(** Base types for links *)")

    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"Record {eClass.name}{eReference.name}_t := {{ {eClass.name}{eReference.name}_t_source : {eClass.name}_t ; {eClass.name}{eReference.name}_t_target : {records_link_multiplicity(eReference)}_t }}.")

            # hack : scheme equality for list
            if eReference.upperBound == 1:
                lst.append(f"Scheme Equality for {eClass.name}{eReference.name}_t.")
            else:
                lst.append(records_link_scheme_equality_list(eClass, eReference))

            lst.append(f"Lemma lem_{eClass.name}{eReference.name}_t_beq_id : forall (e1 e2 : {eClass.name}{eReference.name}_t), {eClass.name}{eReference.name}_t_beq e1 e2 = true -> e1 = e2.")
            lst.append("Proof. Admitted. ")
            lst.append(f"Lemma lem_{eClass.name}{eReference.name}_t_beq_refl : forall (e : {eClass.name}{eReference.name}_t), {eClass.name}{eReference.name}_t_beq e e = true.")
            lst.append("Proof. Admitted. ")

    lst.append(br())

    return join(lst)

def top_element(eClasses):
    lst = []  
    lst.append("(** Data types for element (to build models) *)")
    lst.append("Inductive Element : Set :=")
    for eClass in eClasses:
        lst.append(f"  | {eClass.name}Element : {eClass.name}_t -> Element")
    lst.append(".")  
    lst.append("Scheme Equality for Element.")   
    lst.append(br())

    return join(lst)

def top_link_scheme_equality_list(eClasses):
    lst = []  
    lst.append("Definition Link_beq (c1 : Link) (c2 : Link) : bool :=")
    lst.append("  match c1, c2 with")
    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"  | {eClass.name}{eReference.name}Link o1, {eClass.name}{eReference.name}Link o2 => {eClass.name}{eReference.name}_t_beq o1 o2")
    lst.append("  | _, _ => false")
    lst.append("  end.")

    return join(lst)

def top_link(eClasses):
    lst = []  
    lst.append("(** Data types for link (to build models) *)")
    lst.append("Inductive Link : Set :=")
    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"  | {eClass.name}{eReference.name}Link : {eClass.name}{eReference.name}_t -> Link")
    lst.append(".")
    
    # hack : scheme equality for list
    lst.append(top_link_scheme_equality_list(eClasses))
    lst.append(br())

    return join(lst)

# TODO: refactor
def meta_type(eClasses):
    lst = []  
    lst.append("(** Meta-types (or kinds, to be used in rules) *)")
    lst.append("Inductive ElementKind : Set :=")
    for eClass in eClasses:
        lst.append(f"| {eClass.name}_K")
    lst.append(".")
    lst.append("Scheme Equality for ElementKind.")   
    lst.append(br())
    
    lst.append("Inductive LinkKind : Set :=")
    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"  | {eClass.name}{eReference.name}_K")
    lst.append(".")  
    lst.append("Scheme Equality for LinkKind.")   
    lst.append(br())

    return join(lst)

# TODO: refactor
def reflective_function(eClasses):
    lst = []  
    lst.append("(** Reflective functions (typing : correspondence between abstract types (kinds) and model data) *)")
    # Element
    lst.append("Definition getTypeByEKind (k : ElementKind) : Set :=")
    lst.append("  match k with")
    for eClass in eClasses:
        lst.append(f"  | {eClass.name}_K => {eClass.name}_t")
    lst.append("  end.")
    lst.append(br())

    lst.append("Definition lift_EKind k : (getTypeByEKind k) -> Element := ")
    lst.append("  match k with")
    for eClass in eClasses:
        lst.append(f"  | {eClass.name}_K => {eClass.name}Element")
    lst.append("  end.")
    lst.append(br())

    lst.append("Definition get_E_data (k : ElementKind) (c : Element) : option (getTypeByEKind k) :=")
    lst.append("  match (k,c) as e return (option (getTypeByEKind (fst e))) with")
    for eClass in eClasses:
        lst.append(f"  | ({eClass.name}_K, {eClass.name}Element v)  => Some v")
    lst.append("  | (_ , _) => None")
    lst.append("  end.")
    lst.append(br())

    # Link
    lst.append("Definition getTypeByLKind (k : LinkKind) : Set :=")
    lst.append("  match k with")
    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"  | {eClass.name}{eReference.name}_K => {eClass.name}{eReference.name}_t")
    lst.append("  end.")
    lst.append(br())

    lst.append("Definition lift_LKind k : (getTypeByLKind k) -> Link :=")
    lst.append("  match k with")
    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"  | {eClass.name}{eReference.name}_K => {eClass.name}{eReference.name}Link")
    lst.append("  end.")
    lst.append(br())

    lst.append("Definition get_L_data (t : LinkKind) (c : Link) : option (getTypeByLKind t) :=")
    lst.append("  match (t,c) as e return (option (getTypeByLKind (fst e))) with")
    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"  | ({eClass.name}{eReference.name}_K, {eClass.name}{eReference.name}Link v)  => Some v")
    lst.append("  | (_ , _) => None")
    lst.append("  end.")
    lst.append(br())

    return join(lst)
    
# TODO: refactor
def type_instance(metamodel):
    lst = []  
    lst.append("(** Typeclass Instance *)")
    lst.append(f"Definition {metamodel.name}MM : Metamodel :=")
    lst.append("{|")
    lst.append("  ElementType := Element ;")
    lst.append("  LinkType := Link ;")
    lst.append("  elements_eqdec := Element_beq ;")
    lst.append("  links_eqdec := Link_beq")
    lst.append("|}.")
    lst.append(br())

    lst.append("#[export]")
    lst.append(f"Instance {metamodel.name}ElementDenotation : Denotation Element ElementKind :=")
    lst.append("{")
    lst.append("  denoteDatatype := getTypeByEKind ;")
    lst.append("  unbox := get_E_data ;")
    lst.append("  constructor := lift_EKind ;")
    lst.append("}.")
    lst.append(br())

    lst.append("#[export]")
    lst.append(f"Instance {metamodel.name}LinkDenotation : Denotation Link LinkKind :=")
    lst.append("{")
    lst.append("  denoteDatatype := getTypeByLKind ;")
    lst.append("  unbox := get_L_data ;")
    lst.append("  constructor := lift_LKind ;")
    lst.append("}.")
    lst.append(br())

    lst.append("#[export]")
    lst.append(f"Instance {metamodel.name}Metamodel : ModelingMetamodel {metamodel.name}MM :=")
    lst.append("{")
    lst.append(f"  elements := {metamodel.name}ElementDenotation ;")
    lst.append(f"  links := {metamodel.name}LinkDenotation ;")
    lst.append("}.")
    lst.append(br())

    lst.append(f"Definition {metamodel.name}Model := Model {metamodel.name}MM.")
    lst.append(br())

    return join(lst)


# TODO: refactor
def general_function(eClasses, metamodel):
    lst = []  
    lst.append("(** General functions (used in transformations) *)")

    for eClass in eClasses:
        for eReference in eClass.eReferences:
            lst.append(f"Fixpoint get{eClass.name}{eReference.name}OnLinks ({arg(eClass.name[0])} : {eClass.name}_t) (l : list Link) : option ({records_link_multiplicity(eReference)}_t) :=")
            lst.append(f"match l with")
            lst.append(f"  | ({eClass.name}{eReference.name}Link x) :: l1 =>")
            lst.append(f"    if {eClass.name}_t_beq x.({eClass.name}{eReference.name}_t_source) {arg(eClass.name[0])}")
            lst.append(f"      then (Some x.({eClass.name}{eReference.name}_t_target))")
            lst.append(f"      else get{eClass.name}{eReference.name}OnLinks {arg(eClass.name[0])} l1")
            lst.append(f"  | _ :: l1 => get{eClass.name}{eReference.name}OnLinks {arg(eClass.name[0])} l1")
            lst.append( "  | nil => None")
            lst.append("end.")
            lst.append(br())

            lst.append(f"Definition get{eClass.name}{eReference.name} ({arg(eClass.name[0])} : {eClass.name}_t) (m : {metamodel.name}Model) : option ({records_link_multiplicity(eReference)}_t) :=")
            lst.append(f"  get{eClass.name}{eReference.name}OnLinks {arg(eClass.name[0])} m.(modelLinks).")
            lst.append(br())

    lst.append(br())

    return join(lst)


def useful_lemma(eClasses, metamodel):
    lst = []  
    lst.append("(** Useful lemmas *)")

    lst.append(f"Lemma {metamodel.name}_invert : ")
    lst.append("  forall (k: ElementKind) (t1 t2: getTypeByEKind k),")
    lst.append("    constructor k t1 = constructor k t2 -> t1 = t2.")
    lst.append("Proof. Admitted. ")
    lst.append(br())

    lst.append(f"Lemma Element_dec : ")
    lst.append("  forall (a: Element),")
    tmp_lst = []
    for eClass in eClasses:
        tmp_lst.append(f"(instanceof {eClass.name}_K a) = true")
    lst.append("\/".join(tmp_lst))
    lst.append(".")
    lst.append("Proof. Admitted. ")
    lst.append(br())

    for eClass in eClasses:
        lst.append(f"Lemma {eClass.name}Element_cast :")
        lst.append( "  forall x y,")
        lst.append(f"    unbox {eClass.name}_K x = return y -> {eClass.name}Element y = x.")
        lst.append("Proof. Admitted. ")
        lst.append(br())

    lst.append(br())

    return join(lst)

def genCoqFile(mm_root, eClasses):
    s = ""
    s += imports_native()
    s += imports_coqtl()
    s += records_elem(eClasses)
    s += records_link(eClasses)
    s += top_element(eClasses)
    s += top_link(eClasses)
    s += meta_type(eClasses)
    s += reflective_function(eClasses)
    s += type_instance(mm_root)
    s += general_function(eClasses, mm_root)
    s += useful_lemma(eClasses, mm_root)

    return s

def writeToFile(ecore_path):
    '''
    Contracts: given a ecore file path, write its coqTL model file in the same location, return this ecore metamodel name and the output location.
    '''
    ecore_dir = os.path.dirname(ecore_path)
    rset = ResourceSet()
    resource = rset.get_resource(ecore_path)
    mm_root = resource.contents[0]
    rset.metamodel_registry[mm_root.nsURI] = mm_root
    eClasses = mm_root.eClassifiers
    output_path = os.path.join(ecore_dir, f'{mm_root.name}.v')
    coq_file = genCoqFile(mm_root, eClasses)

    write(output_path, coq_file)

    return mm_root.name, output_path


if __name__ == '__main__':
    args = sys.argv
    if len(args) >= 2:
        ecore_path = args[1]
        mmname, output_dir = writeToFile(ecore_path)
        print(f"    [output] {mmname} metamodel is generated : {output_dir} . ")
    else:
        print(
        '''
    [usage] 
        * python main.py ecore_path
        ''')










