

(********************************************************************
	@name Coq declarations for metamodel: <movies>
	@date 2021/10/17 11:34:17
	@description Automatically generated by Ecore2Coq transformation.
 ********************************************************************)

(* Coq libraries *)
Require Import String.
Require Import Bool.
Require Import List.      (* sequence *)
Require Import Multiset.  (* bag *)
Require Import ListSet.   (* set *)
Require Import PeanoNat.
Require Import EqNat.
Require Import Coq.Logic.Eqdep_dec.

From core Require Import 
  utils.Utils
  Metamodel
  modeling.ModelingMetamodel
  Model
  utils.CpdtTactics
  Tactics.

(* Base types *)


Inductive Person : Set :=
  BuildPerson :
  (* name *) string ->
  Person.

Inductive Actor : Set :=
  BuildActor :
  (* Inheritence Attribute *) Person -> 
  Actor.

Inductive Actress : Set :=
  BuildActress :
  (* Inheritence Attribute *) Person -> 
  Actress.

Inductive Group : Set :=
  BuildGroup :
  (* avgRating *) nat ->
  Group.

Inductive Couple : Set :=
  BuildCouple :
  (* Inheritence Attribute *) Group -> 
  Couple.

Inductive Movie : Set :=
  BuildMovie :
  (* title *) string ->
  (* rating *) nat ->
  (* year *) nat ->
  (* type *) nat ->
  Movie.

Inductive Clique : Set :=
  BuildClique :
  (* Inheritence Attribute *) Group -> 
  Clique.


Inductive PersonMovies : Set :=
   BuildPersonMovies :
   Person ->
   list Movie ->
   PersonMovies.

Definition maybeBuildPersonMovies (pe_arg: Person) (mo_arg: option (list Movie)) : option PersonMovies :=
  match pe_arg, mo_arg with
  | pe_arg_succ, Some mo_arg_succ => Some (BuildPersonMovies pe_arg_succ mo_arg_succ)
  | _, _ => None
  end.



Inductive GroupCommonMovies : Set :=
   BuildGroupCommonMovies :
   Group ->
   list Movie ->
   GroupCommonMovies.

Definition maybeBuildGroupCommonMovies (gr_arg: Group) (co_arg: option (list Movie)) : option GroupCommonMovies :=
  match gr_arg, co_arg with
  | gr_arg_succ, Some co_arg_succ => Some (BuildGroupCommonMovies gr_arg_succ co_arg_succ)
  | _, _ => None
  end.

Inductive CoupleP1 : Set :=
   BuildCoupleP1 :
   Couple ->
   Person ->
   CoupleP1.

Definition maybeBuildCoupleP1 (co_arg: Couple) (p1_arg: option (Person)) : option CoupleP1 :=
  match co_arg, p1_arg with
  | co_arg_succ, Some p1_arg_succ => Some (BuildCoupleP1 co_arg_succ p1_arg_succ)
  | _, _ => None
  end.
Inductive CoupleP2 : Set :=
   BuildCoupleP2 :
   Couple ->
   Person ->
   CoupleP2.

Definition maybeBuildCoupleP2 (co_arg: Couple) (p2_arg: option (Person)) : option CoupleP2 :=
  match co_arg, p2_arg with
  | co_arg_succ, Some p2_arg_succ => Some (BuildCoupleP2 co_arg_succ p2_arg_succ)
  | _, _ => None
  end.

Inductive MoviePersons : Set :=
   BuildMoviePersons :
   Movie ->
   list Person ->
   MoviePersons.

Definition maybeBuildMoviePersons (mo_arg: Movie) (pe_arg: option (list Person)) : option MoviePersons :=
  match mo_arg, pe_arg with
  | mo_arg_succ, Some pe_arg_succ => Some (BuildMoviePersons mo_arg_succ pe_arg_succ)
  | _, _ => None
  end.

Inductive CliquePersons : Set :=
   BuildCliquePersons :
   Clique ->
   list Person ->
   CliquePersons.

Definition maybeBuildCliquePersons (cl_arg: Clique) (pe_arg: option (list Person)) : option CliquePersons :=
  match cl_arg, pe_arg with
  | cl_arg_succ, Some pe_arg_succ => Some (BuildCliquePersons cl_arg_succ pe_arg_succ)
  | _, _ => None
  end.



(* Accessors *)
Definition Person_getName (p : Person) : string :=
  match p with BuildPerson  name  => name end.

Definition Actor_getPerson (a : Actor) : Person :=
  match a with BuildActor person  => person end.

Definition Actress_getPerson (a : Actress) : Person :=
  match a with BuildActress person  => person end.

Definition Group_getAvgRating (g : Group) : nat :=
  match g with BuildGroup  avgRating  => avgRating end.

Definition Couple_getGroup (c : Couple) : Group :=
  match c with BuildCouple group  => group end.

Definition Movie_getTitle (m : Movie) : string :=
  match m with BuildMovie  title rating year type  => title end.
Definition Movie_getRating (m : Movie) : nat :=
  match m with BuildMovie  title rating year type  => rating end.
Definition Movie_getYear (m : Movie) : nat :=
  match m with BuildMovie  title rating year type  => year end.
Definition Movie_getType (m : Movie) : nat :=
  match m with BuildMovie  title rating year type  => type end.

Definition Clique_getGroup (c : Clique) : Group :=
  match c with BuildClique group  => group end.


Definition beq_Person (pe_arg1 : Person) (pe_arg2 : Person) : bool :=
( beq_string (Person_getName pe_arg1) (Person_getName pe_arg2) )
.

Definition beq_Actor (ac_arg1 : Actor) (ac_arg2 : Actor) : bool :=
beq_Person (Actor_getPerson ac_arg1) (Actor_getPerson ac_arg2)
.

Definition beq_Actress (ac_arg1 : Actress) (ac_arg2 : Actress) : bool :=
beq_Person (Actress_getPerson ac_arg1) (Actress_getPerson ac_arg2)
.

Definition beq_Group (gr_arg1 : Group) (gr_arg2 : Group) : bool :=
( beq_nat (Group_getAvgRating gr_arg1) (Group_getAvgRating gr_arg2) )
.

Definition beq_Couple (co_arg1 : Couple) (co_arg2 : Couple) : bool :=
beq_Group (Couple_getGroup co_arg1) (Couple_getGroup co_arg2)
.

Definition beq_Movie (mo_arg1 : Movie) (mo_arg2 : Movie) : bool :=
( beq_string (Movie_getTitle mo_arg1) (Movie_getTitle mo_arg2) ) && 
( beq_nat (Movie_getRating mo_arg1) (Movie_getRating mo_arg2) ) && 
( beq_nat (Movie_getYear mo_arg1) (Movie_getYear mo_arg2) ) && 
( beq_nat (Movie_getType mo_arg1) (Movie_getType mo_arg2) )
.

Definition beq_Clique (cl_arg1 : Clique) (cl_arg2 : Clique) : bool :=
beq_Group (Clique_getGroup cl_arg1) (Clique_getGroup cl_arg2)
.


(* Meta-types *)	
Inductive moviesMetamodel_Class : Set :=
  | PersonClass
  | ActorClass
  | ActressClass
  | CoupleClass
  | MovieClass
  | GroupClass
  | CliqueClass
.

Definition moviesMetamodel_getTypeByClass (mocl_arg : moviesMetamodel_Class) : Set :=
  match mocl_arg with
    | PersonClass => Person
    | ActorClass => Actor
    | ActressClass => Actress
    | CoupleClass => Couple
    | MovieClass => Movie
    | GroupClass => Group
    | CliqueClass => Clique
  end.	

Inductive moviesMetamodel_Reference : Set :=
| PersonMoviesReference
| CoupleP1Reference
| CoupleP2Reference
| MoviePersonsReference
| GroupCommonMoviesReference
| CliquePersonsReference
.

Definition moviesMetamodel_getTypeByReference (more_arg : moviesMetamodel_Reference) : Set :=
  match more_arg with
| PersonMoviesReference => PersonMovies
| CoupleP1Reference => CoupleP1
| CoupleP2Reference => CoupleP2
| MoviePersonsReference => MoviePersons
| GroupCommonMoviesReference => GroupCommonMovies
| CliquePersonsReference => CliquePersons
  end.

Definition moviesMetamodel_getERoleTypesByEReference (more_arg : moviesMetamodel_Reference) : Set :=
  match more_arg with
| PersonMoviesReference => (Person * list Movie)
| CoupleP1Reference => (Couple * Person)
| CoupleP2Reference => (Couple * Person)
| MoviePersonsReference => (Movie * list Person)
| GroupCommonMoviesReference => (Group * list Movie)
| CliquePersonsReference => (Clique * list Person)
  end.

(* Generic types *)			
Inductive moviesMetamodel_Object : Set :=
 | Build_moviesMetamodel_Object : 
    forall (mocl_arg: moviesMetamodel_Class), (moviesMetamodel_getTypeByClass mocl_arg) -> moviesMetamodel_Object.

Definition beq_moviesMetamodel_Object (c1 : moviesMetamodel_Object) (c2 : moviesMetamodel_Object) : bool :=
  match c1, c2 with
  | Build_moviesMetamodel_Object PersonClass o1, Build_moviesMetamodel_Object PersonClass o2 => beq_Person o1 o2
  | Build_moviesMetamodel_Object ActorClass o1, Build_moviesMetamodel_Object ActorClass o2 => beq_Actor o1 o2
  | Build_moviesMetamodel_Object ActressClass o1, Build_moviesMetamodel_Object ActressClass o2 => beq_Actress o1 o2
  | Build_moviesMetamodel_Object CoupleClass o1, Build_moviesMetamodel_Object CoupleClass o2 => beq_Couple o1 o2
  | Build_moviesMetamodel_Object MovieClass o1, Build_moviesMetamodel_Object MovieClass o2 => beq_Movie o1 o2
  | Build_moviesMetamodel_Object GroupClass o1, Build_moviesMetamodel_Object GroupClass o2 => beq_Group o1 o2
  | Build_moviesMetamodel_Object CliqueClass o1, Build_moviesMetamodel_Object CliqueClass o2 => beq_Clique o1 o2
  | _, _ => false
  end.

Inductive moviesMetamodel_Link : Set :=
 | Build_moviesMetamodel_Link : 
    forall (more_arg:moviesMetamodel_Reference), (moviesMetamodel_getTypeByReference more_arg) -> moviesMetamodel_Link.

(* FIXME *)
Definition beq_moviesMetamodel_Link (l1 : moviesMetamodel_Link) (l2 : moviesMetamodel_Link) : bool := true.

(* Reflective functions *)
Lemma moviesMetamodel_eqEClass_dec : 
 forall (mocl_arg1:moviesMetamodel_Class) (mocl_arg2:moviesMetamodel_Class), { mocl_arg1 = mocl_arg2 } + { mocl_arg1 <> mocl_arg2 }.
Proof. repeat decide equality. Defined.

Lemma moviesMetamodel_eqEReference_dec : 
 forall (more_arg1:moviesMetamodel_Reference) (more_arg2:moviesMetamodel_Reference), { more_arg1 = more_arg2 } + { more_arg1 <> more_arg2 }.
Proof. repeat decide equality. Defined.

Definition moviesMetamodel_getEClass (moob_arg : moviesMetamodel_Object) : moviesMetamodel_Class :=
   match moob_arg with
  | (Build_moviesMetamodel_Object moob_arg _) => moob_arg
   end.

Definition moviesMetamodel_getEReference (moli_arg : moviesMetamodel_Link) : moviesMetamodel_Reference :=
   match moli_arg with
  | (Build_moviesMetamodel_Link moli_arg _) => moli_arg
   end.

Definition moviesMetamodel_instanceOfEClass (mocl_arg: moviesMetamodel_Class) (moob_arg : moviesMetamodel_Object): bool :=
  if moviesMetamodel_eqEClass_dec (moviesMetamodel_getEClass moob_arg) mocl_arg then true else false.

Definition moviesMetamodel_instanceOfEReference (more_arg: moviesMetamodel_Reference) (moli_arg : moviesMetamodel_Link): bool :=
  if moviesMetamodel_eqEReference_dec (moviesMetamodel_getEReference moli_arg) more_arg then true else false.


Definition moviesMetamodel_toClass (mocl_arg : moviesMetamodel_Class) (moob_arg : moviesMetamodel_Object) : option (moviesMetamodel_getTypeByClass mocl_arg).
Proof.
  destruct moob_arg as [arg1 arg2].
  destruct (moviesMetamodel_eqEClass_dec arg1 mocl_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
    exact (Some arg2).
  - exact None.
Defined.

Definition moviesMetamodel_toReference (more_arg : moviesMetamodel_Reference) (moli_arg : moviesMetamodel_Link) : option (moviesMetamodel_getTypeByReference more_arg).
Proof.
  destruct moli_arg as [arg1 arg2].
  destruct (moviesMetamodel_eqEReference_dec arg1 more_arg) as [e|] eqn:dec_case.
  - rewrite e in arg2.
  	exact (Some arg2).
  - exact None.
Defined.

(* Generic functions *)

Definition moviesMetamodel_Metamodel_Instance : 
  Metamodel :=
  {|
    ModelElement := moviesMetamodel_Object;
    ModelLink := moviesMetamodel_Link;
    elements_eqdec := beq_moviesMetamodel_Object ;
    links_eqdec := beq_moviesMetamodel_Link
  |}.


Definition moviesModel := Model moviesMetamodel_Metamodel_Instance.

Definition moviesMetamodel_toObject (mocl_arg: moviesMetamodel_Class) (t: moviesMetamodel_getTypeByClass mocl_arg) : moviesMetamodel_Object :=
  (Build_moviesMetamodel_Object mocl_arg t).

Definition moviesMetamodel_toLink (more_arg: moviesMetamodel_Reference) (t: moviesMetamodel_getTypeByReference more_arg) : moviesMetamodel_Link :=
  (Build_moviesMetamodel_Link more_arg t).


Fixpoint moviesMetamodel_Person_downcastActor (pe_arg : Person) (l : list moviesMetamodel_Object) : option Actor := 
  match l with
	 | Build_moviesMetamodel_Object ActorClass (BuildActor eSuper ) :: l' => 
		if beq_Person pe_arg eSuper then (Some (BuildActor eSuper )) else (moviesMetamodel_Person_downcastActor pe_arg l')
	 | _ :: l' => (moviesMetamodel_Person_downcastActor pe_arg l')
	 | nil => None
end.

Definition Person_downcastActor (pe_arg : Person) (m : moviesModel) : option Actor :=
  moviesMetamodel_Person_downcastActor pe_arg m.(modelElements).

Fixpoint moviesMetamodel_Person_downcastActress (pe_arg : Person) (l : list moviesMetamodel_Object) : option Actress := 
  match l with
	 | Build_moviesMetamodel_Object ActressClass (BuildActress eSuper ) :: l' => 
		if beq_Person pe_arg eSuper then (Some (BuildActress eSuper )) else (moviesMetamodel_Person_downcastActress pe_arg l')
	 | _ :: l' => (moviesMetamodel_Person_downcastActress pe_arg l')
	 | nil => None
end.

Definition Person_downcastActress (pe_arg : Person) (m : moviesModel) : option Actress :=
  moviesMetamodel_Person_downcastActress pe_arg m.(modelElements).


Fixpoint moviesMetamodel_Group_downcastCouple (gr_arg : Group) (l : list moviesMetamodel_Object) : option Couple := 
  match l with
	 | Build_moviesMetamodel_Object CoupleClass (BuildCouple eSuper ) :: l' => 
		if beq_Group gr_arg eSuper then (Some (BuildCouple eSuper )) else (moviesMetamodel_Group_downcastCouple gr_arg l')
	 | _ :: l' => (moviesMetamodel_Group_downcastCouple gr_arg l')
	 | nil => None
end.

Definition Group_downcastCouple (gr_arg : Group) (m : moviesModel) : option Couple :=
  moviesMetamodel_Group_downcastCouple gr_arg m.(modelElements).

Fixpoint moviesMetamodel_Group_downcastClique (gr_arg : Group) (l : list moviesMetamodel_Object) : option Clique := 
  match l with
	 | Build_moviesMetamodel_Object CliqueClass (BuildClique eSuper ) :: l' => 
		if beq_Group gr_arg eSuper then (Some (BuildClique eSuper )) else (moviesMetamodel_Group_downcastClique gr_arg l')
	 | _ :: l' => (moviesMetamodel_Group_downcastClique gr_arg l')
	 | nil => None
end.

Definition Group_downcastClique (gr_arg : Group) (m : moviesModel) : option Clique :=
  moviesMetamodel_Group_downcastClique gr_arg m.(modelElements).




Fixpoint Person_getMoviesOnLinks (pe_arg : Person) (l : list moviesMetamodel_Link) : option (list Movie) :=
match l with
| (Build_moviesMetamodel_Link PersonMoviesReference (BuildPersonMovies Person_ctr movies_ctr)) :: l' => 
	  if beq_Person Person_ctr pe_arg then Some movies_ctr else Person_getMoviesOnLinks pe_arg l'
| _ :: l' => Person_getMoviesOnLinks pe_arg l'
| nil => None
end.

Definition Person_getMovies (pe_arg : Person) (m : moviesModel) : option (list Movie) :=
  Person_getMoviesOnLinks pe_arg m.(modelLinks).
  
Definition Person_getMoviesObjects (pe_arg : Person) (m : moviesModel) : option (list moviesMetamodel_Object) :=
  match Person_getMovies pe_arg m with
  | Some l => Some (map (moviesMetamodel_toObject MovieClass) l)
  | _ => None
  end.



Fixpoint Couple_getP1OnLinks (co_arg : Couple) (l : list moviesMetamodel_Link) : option (Person) :=
match l with
| (Build_moviesMetamodel_Link CoupleP1Reference (BuildCoupleP1 Couple_ctr p1_ctr)) :: l' => 
	  if beq_Couple Couple_ctr co_arg then Some p1_ctr else Couple_getP1OnLinks co_arg l'
| _ :: l' => Couple_getP1OnLinks co_arg l'
| nil => None
end.

Definition Couple_getP1 (co_arg : Couple) (m : moviesModel) : option (Person) :=
  Couple_getP1OnLinks co_arg m.(modelLinks).
  
Definition Couple_getP1Object (co_arg : Couple) (m : moviesModel) : option (moviesMetamodel_Object) :=
  match Couple_getP1 co_arg m with
  | Some pe_arg => Some (moviesMetamodel_toObject PersonClass pe_arg) 
  | _ => None
  end.
Fixpoint Couple_getP2OnLinks (co_arg : Couple) (l : list moviesMetamodel_Link) : option (Person) :=
match l with
| (Build_moviesMetamodel_Link CoupleP2Reference (BuildCoupleP2 Couple_ctr p2_ctr)) :: l' => 
	  if beq_Couple Couple_ctr co_arg then Some p2_ctr else Couple_getP2OnLinks co_arg l'
| _ :: l' => Couple_getP2OnLinks co_arg l'
| nil => None
end.

Definition Couple_getP2 (co_arg : Couple) (m : moviesModel) : option (Person) :=
  Couple_getP2OnLinks co_arg m.(modelLinks).
  
Definition Couple_getP2Object (co_arg : Couple) (m : moviesModel) : option (moviesMetamodel_Object) :=
  match Couple_getP2 co_arg m with
  | Some pe_arg => Some (moviesMetamodel_toObject PersonClass pe_arg) 
  | _ => None
  end.

Fixpoint Movie_getPersonsOnLinks (mo_arg : Movie) (l : list moviesMetamodel_Link) : option (list Person) :=
match l with
| (Build_moviesMetamodel_Link MoviePersonsReference (BuildMoviePersons Movie_ctr persons_ctr)) :: l' => 
	  if beq_Movie Movie_ctr mo_arg then Some persons_ctr else Movie_getPersonsOnLinks mo_arg l'
| _ :: l' => Movie_getPersonsOnLinks mo_arg l'
| nil => None
end.

Definition Movie_getPersons (mo_arg : Movie) (m : moviesModel) : option (list Person) :=
  Movie_getPersonsOnLinks mo_arg m.(modelLinks).
  
Definition Movie_getPersonsObjects (mo_arg : Movie) (m : moviesModel) : option (list moviesMetamodel_Object) :=
  match Movie_getPersons mo_arg m with
  | Some l => Some (map (moviesMetamodel_toObject PersonClass) l)
  | _ => None
  end.

Fixpoint Group_getCommonMoviesOnLinks (gr_arg : Group) (l : list moviesMetamodel_Link) : option (list Movie) :=
match l with
| (Build_moviesMetamodel_Link GroupCommonMoviesReference (BuildGroupCommonMovies Group_ctr commonMovies_ctr)) :: l' => 
	  if beq_Group Group_ctr gr_arg then Some commonMovies_ctr else Group_getCommonMoviesOnLinks gr_arg l'
| _ :: l' => Group_getCommonMoviesOnLinks gr_arg l'
| nil => None
end.

Definition Group_getCommonMovies (gr_arg : Group) (m : moviesModel) : option (list Movie) :=
  Group_getCommonMoviesOnLinks gr_arg m.(modelLinks).
  
Definition Group_getCommonMoviesObjects (gr_arg : Group) (m : moviesModel) : option (list moviesMetamodel_Object) :=
  match Group_getCommonMovies gr_arg m with
  | Some l => Some (map (moviesMetamodel_toObject MovieClass) l)
  | _ => None
  end.

Fixpoint Clique_getPersonsOnLinks (cl_arg : Clique) (l : list moviesMetamodel_Link) : option (list Person) :=
match l with
| (Build_moviesMetamodel_Link CliquePersonsReference (BuildCliquePersons Clique_ctr persons_ctr)) :: l' => 
	  if beq_Clique Clique_ctr cl_arg then Some persons_ctr else Clique_getPersonsOnLinks cl_arg l'
| _ :: l' => Clique_getPersonsOnLinks cl_arg l'
| nil => None
end.

Definition Clique_getPersons (cl_arg : Clique) (m : moviesModel) : option (list Person) :=
  Clique_getPersonsOnLinks cl_arg m.(modelLinks).
  
Definition Clique_getPersonsObjects (cl_arg : Clique) (m : moviesModel) : option (list moviesMetamodel_Object) :=
  match Clique_getPersons cl_arg m with
  | Some l => Some (map (moviesMetamodel_toObject PersonClass) l)
  | _ => None
  end.


(* Typeclass Instances *)	

#[export]
Instance moviesMetamodel_ElementSum : Sum moviesMetamodel_Object moviesMetamodel_Class :=
{
	denoteSubType := moviesMetamodel_getTypeByClass;
	toSubType := moviesMetamodel_toClass;
	toSumType := moviesMetamodel_toObject;
}.

#[export]
Instance moviesMetamodel_LinkSum : Sum moviesMetamodel_Link moviesMetamodel_Reference :=
{
	denoteSubType := moviesMetamodel_getTypeByReference;
	toSubType := moviesMetamodel_toReference;
	toSumType := moviesMetamodel_toLink;
}.



#[export]
Instance moviesMetamodel_ModelingMetamodel_Instance : 
	ModelingMetamodel moviesMetamodel_Metamodel_Instance :=
{ 
    elements := moviesMetamodel_ElementSum;
    links := moviesMetamodel_LinkSum; 
}.

(* Useful lemmas *)

Lemma movies_invert : 
  forall (mocl_arg: moviesMetamodel_Class) (t1 t2: moviesMetamodel_getTypeByClass mocl_arg), 
    Build_moviesMetamodel_Object mocl_arg t1 = Build_moviesMetamodel_Object mocl_arg t2 -> t1 = t2.
Proof.
  intros. Tactics.dep_inversion H. assumption.
Qed.
