Require
  varieties.monoids theory.groups strong_setoids.
Require Import
  Ring abstract_algebra.

Definition is_ne_0 `(x : R) `{Equiv R} `{RingZero R} `{p : PropHolds (x ≠ 0)} : x ≠ 0 := p.
Definition is_nonneg `(x : R) `{Equiv R} `{Le R} `{RingZero R} `{p : PropHolds (0 ≤ x)} : 0 ≤ x := p.
Definition is_pos `(x : R) `{Equiv R} `{Lt R} `{RingZero R} `{p : PropHolds (0 < x)} : 0 < x := p.

Lemma stdlib_semiring_theory R `{SemiRing R} : Ring_theory.semi_ring_theory 0 1 (+) (.*.) (=).
Proof.
  constructor; intros.
         apply left_identity.
        apply commutativity.
       apply associativity.
      apply left_identity.
     apply left_absorb.
    apply commutativity.
   apply associativity.
  apply distribute_r.
Qed.

(* We cannot apply [left_cancellation (.*.) z] directly in case we have
  no [PropHolds (0 ≠ z)] instance in the context. *)
Section cancellation.
  Context `{e : Equiv A} (op : A → A → A) `{!RingZero A}.

  Lemma left_cancellation_ne_0 `{∀ z, PropHolds (z ≠ 0) → LeftCancellation op z} z : z ≠ 0 → LeftCancellation op z.
  Proof. auto. Qed.

  Lemma right_cancellation_ne_0 `{∀ z, PropHolds (z ≠ 0) → RightCancellation op z} z : z ≠ 0 → RightCancellation op z.
  Proof. auto. Qed.

  Lemma right_cancel_from_left `{!Setoid A} `{!Commutative op} `{!LeftCancellation op z} : 
    RightCancellation op z.
  Proof.
    intros x y E.
    apply (left_cancellation op z).
    now rewrite 2!(commutativity z _).
  Qed.
End cancellation.

Section strong_cancellation.
  Context `{StrongSetoid A} (op : A → A → A).

  Lemma strong_right_cancel_from_left `{!Commutative op} `{!StrongLeftCancellation op z} : 
    StrongRightCancellation op z.
  Proof.
    intros x y E.
    rewrite 2!(commutativity _ z).
    now apply (strong_left_cancellation op z).
  Qed.

  Global Instance strong_left_cancellation_cancel `{!StrongLeftCancellation op z} : LeftCancellation op z | 20.
  Proof.
    intros x y. rewrite <-!tight_apart. intros E1 E2.
    destruct E1. now apply (strong_left_cancellation op).
  Qed.

  Global Instance strong_right_cancellation_cancel `{!StrongRightCancellation op z} : RightCancellation op z | 20.
  Proof.
    intros x y. rewrite <-!tight_apart. intros E1 E2.
    destruct E1. now apply (strong_right_cancellation op).
  Qed.
End strong_cancellation.

Section semiring_props.
  Context `{SemiRing R}.
  Add Ring SR: (stdlib_semiring_theory R).

  Instance mult_ne_0 `{NoZeroDivisors R} x y : PropHolds (x ≠ 0) → PropHolds (y ≠ 0) → PropHolds (x * y ≠ 0).
  Proof.
    intros Ex Ey Exy.
    unfold PropHolds in *.
    apply (no_zero_divisors x); split; eauto.
  Qed.

  Global Instance plus_0_r: RightIdentity (+) 0 := right_identity.
  Global Instance plus_0_l: LeftIdentity (+) 0 := left_identity.
  Global Instance mult_1_l: LeftIdentity (.*.) 1 := left_identity.
  Global Instance mult_1_r: RightIdentity (.*.) 1 := right_identity.

  Global Instance mult_0_l: LeftAbsorb (.*.) 0 := left_absorb.

  Global Instance mult_0_r: RightAbsorb (.*.) 0.
  Proof. intro. ring. Qed.

  Lemma plus_mult_distr_r x y z: (x + y) * z = x * z + y * z. Proof. ring. Qed.
  Lemma plus_mult_distr_l x y z: x * (y + z) = x * y + x * z. Proof. ring. Qed.  

  Global Instance: ∀ r : R, @Monoid_Morphism R R _ _ (0:R) (0:R) (+) (+) (r *.).
  Proof.
   repeat (constructor; try apply _). 
    apply distribute_l.
   apply right_absorb.
  Qed.
End semiring_props.

(* Due to bug #2528 *)
Hint Extern 3 (PropHolds (_ * _ ≠ 0)) => eapply @mult_ne_0 : typeclass_instances.

Section semiringmor_props. 
  Context `{SemiRing_Morphism A B f}.

  Lemma preserves_0: f 0 = 0.
  Proof (preserves_mon_unit (f:=f)). 
  Lemma preserves_1: f 1 = 1.
  Proof (preserves_mon_unit (f:=f)).
  Lemma preserves_mult: ∀ x y, f (x * y) = f x * f y.
  Proof. intros. apply preserves_sg_op. Qed.
  Lemma preserves_plus: ∀ x y, f (x + y) = f x + f y.
  Proof. intros. apply preserves_sg_op. Qed.

  Instance: SemiRing B := semiringmor_b.

  Lemma preserves_2: f 2 = 2.
  Proof. rewrite preserves_plus. now rewrite preserves_1. Qed.

  Lemma preserves_3: f 3 = 3.
  Proof. now rewrite ?preserves_plus, ?preserves_1. Qed.

  Lemma preserves_4: f 4 = 4.
  Proof. now rewrite ?preserves_plus, ?preserves_1. Qed.

  Context `{!Injective f}.
  Instance injective_ne_0 x : PropHolds (x ≠ 0) → PropHolds (f x ≠ 0).
  Proof. intros. rewrite <-preserves_0. now apply (jections.injective_ne f). Qed.

  Lemma injective_ne_1 x : x ≠ 1 → f x ≠ 1.
  Proof. intros. rewrite <-preserves_1. now apply (jections.injective_ne f). Qed.
End semiringmor_props.

(* Due to bug #2528 *)
Hint Extern 12 (PropHolds (_ _ ≠ 0)) => eapply @injective_ne_0 : typeclass_instances.

Lemma stdlib_ring_theory R `{Ring R} : 
  Ring_theory.ring_theory 0 1 (+) (.*.) (λ x y, x - y) (-) (=).
Proof.
 constructor; intros.
         apply left_identity.
        apply commutativity.
       apply associativity.
      apply left_identity.
     apply commutativity.
    apply associativity.
   apply distribute_r.
  reflexivity.
 apply (right_inverse x).
Qed.

Section ring_props. 
  Context `{Ring R}.

  Add Ring R: (stdlib_ring_theory R).

  Instance: LeftAbsorb (.*.) 0.
  Proof. intro. ring. Qed.

  Global Instance Ring_Semi: SemiRing R.
  Proof. repeat (constructor; try apply _). Qed.

  Lemma opp_involutive x: - -x = x. Proof. ring. Qed.
  Lemma plus_opp_r x: x + -x = 0. Proof. ring. Qed.
  Lemma plus_opp_l x: -x + x = 0. Proof. ring. Qed.
  Lemma opp_swap_r x y: x + - y = - (y - x). Proof. ring. Qed.
  Lemma opp_swap_l x y: -x + y = - (x - y). Proof. ring. Qed.
  Lemma opp_distr x y: - (x + y) = - x + - y. Proof. ring. Qed.
  Lemma opp_mult a: -a = -1 * a. Proof. ring. Qed.
  Lemma opp_mult_distr_l a b: -(a * b) = -a * b. Proof. ring. Qed.
  Lemma opp_mult_distr_r a b: -(a * b) = a * -b. Proof. ring. Qed.
  Lemma opp_mult_opp a b: -a * -b = a * b. Proof. ring. Qed.
  Lemma opp_0: -0 = 0. Proof. ring. Qed.

  Lemma equal_by_zero_sum x y : x + - y = 0 ↔ x = y.
  Proof. 
    split; intros E. 
     rewrite <- (plus_0_l y). rewrite <- E. ring. 
    rewrite E. ring.
  Qed.

  Lemma flip_opp_zero x : -x = 0 ↔ x = 0.
  Proof.
    split; intros E.
     apply (injective (-)). now rewrite E, opp_0.
    now rewrite E, opp_0.
  Qed.
  
  Lemma flip_opp_ne_0 x : -x ≠ 0 ↔ x ≠ 0.
  Proof. split; intros E ?; apply E; now apply flip_opp_zero. Qed.

  Lemma opp_zero_prod_l x y : -x * y = 0 ↔ x * y = 0.
  Proof.
    split; intros E.
     apply (injective (-)). now rewrite opp_mult_distr_l, opp_0.
    apply (injective (-)). now rewrite opp_mult_distr_l, opp_involutive, opp_0.
  Qed.

  Lemma opp_zero_prod_r x y : x * -y = 0 ↔ x * y = 0.
  Proof. rewrite (commutativity x (-y)), (commutativity x y). apply opp_zero_prod_l. Qed.

  Lemma units_dont_divide_zero (x: R) `{!RingMultInverse x} `{!RingUnit x}: ¬ ZeroDivisor x.
    (* todo: we don't want to have to mention RingMultInverse *)
  Proof with try ring.
   intros [x_nonzero [z [z_nonzero xz_zero]]].
   apply z_nonzero.
   transitivity (1 * z)...
   rewrite <- ring_unit_mult_inverse.
   transitivity (x * z * ring_mult_inverse x)...
   rewrite xz_zero...
  Qed.

  Context `{!NoZeroDivisors R} `{∀ x y, Stable (x = y)}.

  Global Instance ring_mult_left_cancel:  ∀ z, PropHolds (z ≠ 0) → LeftCancellation (.*.) z.
  Proof.
   intros z z_nonzero x y E.
   apply stable.
   intro U.
   apply (mult_ne_0 z (x +- y) (is_ne_0 z)). 
    intro. apply U. now apply equal_by_zero_sum.
   rewrite distribute_l, E. ring.
  Qed.

  Global Instance: ∀ z, PropHolds (z ≠ 0) → RightCancellation (.*.) z.
  Proof. intros ? ?. apply (right_cancel_from_left (.*.)). Qed.
End ring_props.

Section integral_domain_props. 
  Context `{IntegralDomain R}.

  Instance intdom_nontrivial_apart `{Apart R} `{!TrivialApart R} : 
    PropHolds (1 ⪥ 0).
  Proof. apply strong_setoids.ne_apart. solve_propholds. Qed.
End integral_domain_props. 

(* Due to bug #2528 *)
Hint Extern 6 (PropHolds (1 ⪥ 0)) => eapply @intdom_nontrivial_apart : typeclass_instances.

Section ringmor_props. 
  Context `{Ring A} `{Ring B} {f : A → B} `{!SemiRing_Morphism f}.

  Lemma preserves_opp x : f (- x) = - f x.
  Proof. apply groups.preserves_inv. Qed.

  Lemma preserves_minus x y : f (x - y) = f x - f y.
  Proof.
    rewrite <-preserves_opp.
    apply preserves_plus.
  Qed.

  Lemma injective_preserves_0 : (∀ x, f x = 0 → x = 0) → Injective f.
  Proof.
    intros E1.
    split; try apply _. intros x y E.
    apply equal_by_zero_sum.
    apply E1.
    rewrite preserves_minus, E.
    now apply plus_opp_r.
  Qed.
End ringmor_props.

Section from_another_ring.
  Context `{Ring A} `{Setoid B} 
   `{plus : RingPlus B} `{RingZero B} `{mult : RingMult B} `{RingOne B} `{opp : GroupInv B}
    (f : B → A) `{!Injective f}
    (plus_correct : ∀ x y, f (x + y) = f x + f y) (zero_correct : f 0 = 0) 
    (mult_correct : ∀ x y, f (x * y) = f x * f y) (one_correct : f 1 = 1) (opp_correct : ∀ x, f (-x) = -f x).

  Instance: Setoid_Morphism f := injective_mor f.
  Add Ring A : (stdlib_ring_theory A).

  Instance: Proper ((=) ==> (=) ==> (=)) plus.
  Proof. intros ? ? E1 ? ? E2. apply (injective f). rewrite 2!plus_correct. apply sg_op_proper; now apply sm_proper. Qed.

  Instance: Proper ((=) ==> (=) ==> (=)) mult.
  Proof. intros ? ? E1 ? ? E2. apply (injective f). rewrite 2!mult_correct. apply sg_op_proper; now apply sm_proper. Qed.

  Instance: Proper ((=) ==> (=)) opp.
  Proof. intros ? ? E1. apply (injective f). rewrite 2!opp_correct. now apply sm_proper; apply sm_proper. Qed.

  Lemma projected_ring: Ring B.
  Proof.
    repeat split; try apply _; repeat intro; apply (injective f);
      repeat (rewrite plus_correct || rewrite zero_correct 
      || rewrite mult_correct || rewrite one_correct 
      || rewrite opp_correct); ring.
  Qed.
End from_another_ring.

Section from_stdlib_semiring_theory.
  Context
    `(H: @semi_ring_theory R zero one pl mu e)
    `{!@Setoid R e}
    `{!Proper (e ==> e ==> e) pl}
    `{!Proper (e ==> e ==> e) mu}.

  Add Ring R2: H.

  Definition from_stdlib_semiring_theory: @SemiRing R e pl mu zero one.
  Proof.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, ringzero_is_monoidunit, ringplus_is_semigroupop, 
     ringone_is_monoidunit, ringmult_is_semigroupop, ring_zero, ring_mult, ring_plus; ring.
  Qed.
End from_stdlib_semiring_theory.

Section from_stdlib_ring_theory.
  Context
    `(H: @ring_theory R zero one pl mu mi op e)
    `{!@Setoid R e}
    `{!Proper (e ==> e ==> e) pl}
    `{!Proper (e ==> e ==> e) mu}
    `{!Proper (e ==> e) op}.

  Add Ring R3: H.

  Definition from_stdlib_ring_theory: @Ring R e pl mu zero one op.
  Proof.
   repeat (constructor; try assumption); repeat intro
   ; unfold equiv, mon_unit, sg_op, ringzero_is_monoidunit, ringplus_is_semigroupop, 
     ringone_is_monoidunit, ringmult_is_semigroupop, ring_mult, ring_plus, group_inv; ring.
  Qed.
End from_stdlib_ring_theory.

Section morphism_composition.
  Context (A B C: Type)
    `{!RingMult A} `{!RingPlus A} `{!RingOne A} `{!RingZero A} `{!Equiv A}
    `{!RingMult B} `{!RingPlus B} `{!RingOne B} `{!RingZero B} `{!Equiv B}
    `{!RingMult C} `{!RingPlus C} `{!RingOne C} `{!RingZero C} `{!Equiv C}
    (f: A → B) (g: B → C).

  Global Instance id_semiring_morphism `{!SemiRing A}: SemiRing_Morphism id := {}.

  Global Instance compose_semiring_morphisms `{!SemiRing_Morphism f} `{!SemiRing_Morphism g} : 
    SemiRing_Morphism (g ∘ f).
  Proof.
    constructor; try apply _.
     now apply semiringmor_a.
    now apply semiringmor_b.
  Qed.
End morphism_composition.

Instance semiring_morphism_proper {A B eA eB pA mA zA oA pB mB zB oB} : 
  Proper ((=) ==> (=)) (@SemiRing_Morphism A B eA eB pA mA zA oA pB mB zB oB).
Proof.
  assert (∀ (f g : A → B), g = f → SemiRing_Morphism f → SemiRing_Morphism g) as P.
   intros f g E [? ? ? ?].
   now split; try apply _; eapply groups.monoid_morphism_proper; eauto.
  intros f g ?; split; intros Mor.
   apply P with f. destruct Mor. now symmetry. now apply _.
  now apply P with g.
Qed.
