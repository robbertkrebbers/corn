Set Automatic Introduction.

Require Import
  Program
  theory.categories
  interfaces.functors
  abstract_algebra
  interfaces.sequences
  canonical_names.

Section contents.

  Context `{Sequence sq}.

  (* Some derived properties about inject, extend, and fmap: *)

  Lemma inject_epi `{Setoid A} `{Equiv B} `{SemiGroupOp B} `{MonoidUnit B}
    (f g: sq A → B): Monoid_Morphism f → Monoid_Morphism g →
      f ∘ inject A = g ∘ inject A → f = g.
  Proof with intuition.
   intros.
   pose proof (@setoidmor_a _ _ _ _ f _).
   pose proof (@monmor_b _ _ _ _ _ _ _ _ g _).
   pose proof (sequence_only_extend_commutes sq (f ∘ inject A) _) as E.
   pose proof (_: Setoid_Morphism (f ∘ inject A)) as cm.
   rewrite (E f), (E g)...
    apply (sequence_extend_morphism sq)...
    apply cm.
   apply cm.
  Qed.

  Lemma extend_comp
    `{Equiv A}
    `{Equiv B} `{SemiGroupOp B} `{MonoidUnit B}
    `{Equiv C} `{SemiGroupOp C} `{MonoidUnit C}
    (f: B → C) (g: A → B): Monoid_Morphism f → Setoid_Morphism g →
    extend (f ∘ g) = f ∘ extend g.
  Proof with try apply _.
   intros.
   pose proof (@setoidmor_a _ _ _ _ g _).
   pose proof (@monmor_a _ _ _ _ _ _ _ _ f _).
   pose proof (@monmor_b _ _ _ _ _ _ _ _ f _).
   symmetry.
   apply (sequence_only_extend_commutes sq (f ∘ g))...
   symmetry.
   rewrite <- (sequence_extend_commutes sq g _) at 1.
   apply sm_proper.
  Qed.

  Lemma extend_inject `{Setoid A}: extend (inject A) = @id (sq A).
  Proof with try apply _.
   symmetry. apply (sequence_only_extend_commutes sq)...
   apply sm_proper.
  Qed.

  Lemma fmap_alt `{Equiv A} `{Equiv B} (f: A → B):
    Setoid_Morphism f → extend (inject B ∘ f) = (fmap sq f: sq A → sq B).
  Proof with try apply _.
   intros.
   pose proof (@setoidmor_a _ _ _ _ f _).
   pose proof (@setoidmor_b _ _ _ _ f _).
   symmetry.
   apply (sequence_only_extend_commutes sq (inject B ∘ f) _)...
   symmetry.
   apply (sequence_inject_natural sq)...
  Qed.

  Lemma fold_inject `{Monoid A}: fold sq ∘ inject A = id.
  Proof. apply (sequence_extend_commutes sq id). apply _. Qed.

  Lemma fold_map `{Setoid A} `{Monoid B} (f: A → B):
    Setoid_Morphism f → extend f = fold sq ∘ fmap sq f.
  Proof with try apply _.
   intros.
   symmetry.
   apply (sequence_only_extend_commutes sq _)...
   symmetry.
   change (f = extend id ∘ (@fmap _ _ _ _ sq _ _ B f ∘ inject A)).
   rewrite <- (sequence_inject_natural sq f _).
   change (f = fold sq ∘ inject B ∘ f).
   rewrite fold_inject.
   rewrite compose_id_left.
   apply sm_proper.
  Qed.

End contents.

(* In the context of a SemiRing, we have two particularly useful folds: sum and product. *)

Section semiring_folds.

  Context `{SemiRing R} `{Sequence sq}.

  Definition sum: sq R → R := @fold sq _ _ _ (+).
  Definition product: sq R → R := @fold sq _ _ _ ring_mult.

  (* These are implicitly Monoid_Morphisms, and we also easily have: *)

  Lemma distribute_sum (a: R): (a *) ∘ sum = sum ∘ fmap sq (a *).
  Proof with try apply _.
   unfold sum, fold.
   rewrite <- extend_comp...
   rewrite compose_id_right.
   rewrite fold_map...
   apply sm_proper.
  Qed.

End semiring_folds.