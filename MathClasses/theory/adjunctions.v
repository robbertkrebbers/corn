(** We prove the equivalence of the two definitions of adjunction. *)

Require Import
  Relation_Definitions
  abstract_algebra theory.setoids interfaces.functors theory.categories
  workaround_tactics theory.jections.
Require dual.

Local Hint Unfold id compose: typeclass_instances. (* todo: move *)
Local Existing Instance injective_mor.
Local Existing Instance surjective_mor.

Lemma equal_because_sole `{Setoid T} (P: T → Prop) x: is_sole P x → forall y z, P y → P z → y = z.
Proof. firstorder. Qed. (* todo: move *)

Section for_phiAdjunction.

  (* MacLane p79/p80, showing that from an phiAdjunction we can make
   both a etaAdjunction and a etaepsilonAdjunction. *)

  Context `(phiAdjunction).

  Implicit Arguments phi [[d] [c]].

  Let hint''''' := phi_adjunction_bijective F G.
  Let hint'''' x y: Injective (@phi x y) := _.
  Let hint := phi_adjunction_left_functor F G.
  Let hint' := phi_adjunction_right_functor F G.
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.
   (* Waiting for the new proof engine ... *)

  Lemma phi_adjunction_natural_right_inv `(g: c ⟶ G d) `(h: c' ⟶ c): phi⁻¹ (g ◎ h) = phi⁻¹ g ◎ fmap F h.
  Proof with try reflexivity; try apply _.
   intros.
   apply (injective phi).
   rewrite surjective_applied...
   rewrite phi_adjunction_natural_right...
   rewrite surjective_applied...
  Qed.

  Lemma phi_adjunction_natural_left_inv `(g: c ⟶ G d) `(k: d ⟶ d'): phi⁻¹ (fmap G k ◎ g) = k ◎ phi⁻¹ g.
  Proof with try reflexivity; try apply _.
   intros.
   apply (injective phi).
   rewrite surjective_applied...
   rewrite phi_adjunction_natural_left...
   rewrite surjective_applied...
  Qed.

  Let eta: id ⇛ G ∘ F := λ c, phi (cat_id: F c ⟶ F c).
  Let epsilon: F ∘ G ⇛ id := λ d, phi ⁻¹ (cat_id: G d ⟶ G d).

  Global Instance eta_natural: NaturalTransformation eta.
  Proof with try reflexivity; try apply _.
   intros x' x h.
   change (phi cat_id ◎ h = fmap G (fmap F h) ◎ phi cat_id).
   rewrite <- phi_adjunction_natural_left, <- phi_adjunction_natural_right, left_identity, right_identity...
  Qed.

  Global Instance: NaturalTransformation epsilon.
  Proof with try reflexivity; try apply _.
   intros d d' f.
   change ((phi ⁻¹) cat_id ◎ fmap F (fmap G f) = f ◎ (phi ⁻¹) cat_id).
   rewrite <- phi_adjunction_natural_left_inv, <- phi_adjunction_natural_right_inv, left_identity, right_identity...
  Qed.

  Lemma phi_in_terms_of_eta `(f: F x ⟶ a): phi f = fmap G f ◎ eta x.
  Proof.
   rewrite <- (right_identity f) at 1.
   rewrite phi_adjunction_natural_left. reflexivity. apply _.
  Qed.

  Lemma phi_in_terms_of_epsilon `(g: x ⟶ G a): phi⁻¹ g = epsilon a ◎ fmap F g.
  Proof.
   rewrite <- (left_identity g) at 1.
   apply phi_adjunction_natural_right_inv.
  Qed.

  Definition univwit (c : C) (d : D): (c ⟶ G d) → (F c ⟶ d) := phi⁻¹.

  Instance: ∀ c, UniversalArrow (eta c: c ⟶ G (F c)) (univwit c).
  Proof.
   unfold univwit.
   constructor; unfold compose.
    rewrite <- (phi_in_terms_of_eta ((phi ⁻¹) f)).
    symmetry.
    apply surjective_applied.
   intros ? E.
   rewrite E.
   rewrite <- (phi_in_terms_of_eta y).
   symmetry.
   apply bijective_applied.
  Qed.

  Instance phiAdjunction_etaAdjunction: etaAdjunction F G eta univwit := {}.

  Instance phiAdjunction_etaepsilonAdjunction: etaepsilonAdjunction F G eta epsilon.
  Proof with try apply _.
   constructor; try apply _; intro x.
    rewrite <- @phi_in_terms_of_eta.
    unfold epsilon. apply surjective_applied.
   rewrite <- @phi_in_terms_of_epsilon.
   unfold eta. apply surjective_applied.
  Qed.

  (* On a side note, if we let F and G map between the duals of C and D, the adjunction is reversed: *)

  Goal @phiAdjunction D _ _ _ _ C _ _ _ _ G (dual.fmap_op G) F (dual.fmap_op F) (λ d c, (@phi c d)⁻¹)
    (λ d c, @phi c d).
  Proof with try apply _.
   constructor; intros...
     pose proof (phi_adjunction_bijective F G)...
    change (d' ⟶ d) in k.
    change (d ⟶ G c) in f.
    change ((phi ⁻¹) (f ◎ k) = (phi ⁻¹) f ◎ fmap F k).
    apply (injective (@phi d' c)).
    rewrite surjective_applied.
    rewrite phi_adjunction_natural_right...
    rewrite surjective_applied.
    reflexivity.
   change (c ⟶ c') in h.
   change (d ⟶ G c) in f.
   change ((phi ⁻¹) (fmap G h ◎ f) = h ◎ (phi ⁻¹) f).
   apply (injective (@phi d c')).
   rewrite surjective_applied.
   rewrite phi_adjunction_natural_left...
   rewrite surjective_applied.
   reflexivity.
  Qed.

End for_phiAdjunction.

Section for_etaAdjunction.

  Context `(etaAdjunction).

  Let hint := eta_adjunction_left_functor F G.
  Let hint' := eta_adjunction_right_functor F G.
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.

  Let phi x a (g: F x ⟶ a): (x ⟶ G a) := fmap G g ◎ eta x.

  Instance: ∀ (c: C) (d: D), Inverse (@phi c d) := uniwit.

  Instance: ∀ x a, Surjective (@phi x a).
  Proof with try apply _.
   unfold phi.
   repeat intro.
   constructor.
    intros x0 y E. symmetry.
    rewrite <- E.
    apply (eta_adjunction_universal F G x).
   constructor...
   intros ?? E. rewrite E. reflexivity.
  Qed.

  Instance: ∀ x a, Injective (@phi x a).
  Proof with try reflexivity; try apply _; auto.
   repeat intro. constructor... unfold phi. repeat intro.
   apply (equal_because_sole _ _ (eta_adjunction_universal F G _ _ (fmap G x0 ◎ eta x))); unfold compose...
  Qed.

  Instance: ∀ x a, Bijective (@phi x a) := {}.

  Instance etaAdjunction_phiAdjunction: phiAdjunction F G phi.
  Proof with try reflexivity; try apply _.
   unfold phi. unfold id in *. unfold compose in eta.
   constructor...
    repeat intro. unfold compose.
    rewrite associativity...
    rewrite preserves_comp...
   repeat intro. unfold compose.
   rewrite preserves_comp...
   rewrite <- associativity.
   pose proof (eta_adjunction_natural F G c' c h) as P.
   change (eta c ◎ h = fmap G (fmap F h) ◎ eta c') in P.
   rewrite <- P.
   rewrite associativity...
  Qed.

End for_etaAdjunction.

Section for_etaepsilonAdjunction.

  Context `(etaepsilonAdjunction).

  Let hint := etaepsilon_adjunction_left_functor F G.
  Let hint' := etaepsilon_adjunction_right_functor F G.
  Let hint'' := functor_from G.
  Let hint''' := functor_to G.
  Let hint'''' := etaepsilon_adjunction_eta_natural F G.
  Let hint''''' := etaepsilon_adjunction_epsilon_natural F G.

  Let phi `(f: F c ⟶ d): (c ⟶ G d) := fmap G f ◎ eta c.
  Instance uniwit c d: Inverse (phi c d) := λ f, epsilon d ◎ fmap F f.

  Instance etaepsilonAdjunction_etaAdjunction: etaAdjunction F G eta uniwit.
  Proof with try apply _.
   constructor...
   unfold uniwit.
   constructor; unfold compose.
    rewrite preserves_comp...
    pose proof (etaepsilon_adjunction_eta_natural F G c (G d) f) as P.
    change (eta (G d) ◎ f = fmap G (fmap F f) ◎ eta c) in P.
    rewrite <- associativity.
    rewrite <- P.
    rewrite associativity.
    pose proof (etaepsilon_adjunction_identity_at_G F G d) as Q.
    simpl in Q.
    rewrite Q.
    symmetry.
    apply left_identity.
   intros y E. rewrite E. clear E f.
   rewrite preserves_comp...
   rewrite associativity.
   pose proof (etaepsilon_adjunction_epsilon_natural F G (F c) d y) as P.
   change (epsilon d ◎ fmap F (fmap G y) = y ◎ epsilon (F c)) in P.
   rewrite P.
   rewrite <- associativity.
   pose proof (etaepsilon_adjunction_identity_at_F F G c) as Q.
   simpl in Q.
   rewrite Q.
   symmetry.
   apply right_identity.
  Qed.

  Instance etaepsilonAdjunction_phiAdjunction: phiAdjunction F G phi.
  Proof. apply etaAdjunction_phiAdjunction, _. Qed.

End for_etaepsilonAdjunction.
