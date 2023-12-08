(** * Metamodel **)


Record Metamodel :=
{
    ElementType: Set;
    LinkType: Set;
    
    elements_eq_dec: forall (a:ElementType) (b:ElementType), {a=b} + {a<>b} ; 
  
    elements_beq : ElementType -> ElementType -> bool := fun a b => if elements_eq_dec a b then true else false ;
  

}.

Lemma beq_correct : 
  forall M : Metamodel,
  forall a b, M.(elements_beq) a b = true -> a = b.
Proof.
  intros.
  unfold elements_beq in H.
  destruct (elements_eq_dec M a b) ; [ congruence | discriminate ]. 
Qed.

Lemma beq_refl : 
  forall M : Metamodel,
  forall a, M.(elements_beq) a a = true.
Proof.
  intros.
  unfold elements_beq.
  destruct (elements_eq_dec M a a) ; [ reflexivity |  ].
  contradict n ; reflexivity.
Qed.
