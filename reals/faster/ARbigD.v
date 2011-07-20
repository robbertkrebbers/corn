Require Import
  Program QArith ZArith BigZ Qpossec
  MetricMorphisms Qmetric Qdlog ARArith
  theory.int_pow theory.nat_pow
  stdlib_rationals stdlib_binary_integers fast_integers dyadics.

Add Field Q : (dec_fields.stdlib_field_theory Q).

Notation bigD := (Dyadic bigZ).
Instance inject_bigZ_Q: Cast bigZ Q_as_MetricSpace := inject_Z ∘ BigZ.to_Z.
Instance inject_Z_bigD: Cast Z bigD := dy_inject ∘ BigZ.of_Z.
Instance inject_N_bigZ: Cast N bigZ := BigZ.of_Z ∘ Z_of_N.
Instance inject_bigD_Q: Cast bigD Q_as_MetricSpace := DtoQ inject_bigZ_Q.

Lemma inject_bigD_Q_correct x : cast bigD Q x = 'mant x * 2 ^ (cast bigZ Z (expo x)).
Proof.
  unfold cast at 1, inject_bigD_Q.
  rewrite (DtoQ_correct _ _ (reflexivity x)).
  unfold DtoQ_slow.
  now rewrite (preserves_int_pow_exp (f:=cast bigZ Z)).
Qed.

(* 
  We use BigZ.div and BigZ.shiftl because we don't have any theory on euclid and shiftr
  in math-classes yet. Moreover, BigZ.shiftl behaves as shiftr on its negative domain,
  which is quite convenient here.
*)
Program Instance bigD_div: AppDiv bigD := λ x y k,
  BigZ.div (BigZ.shiftl (mant x) (-('k - 1) + expo x - expo y)) (mant y) ▼ ('k - 1).

Lemma Qdiv_bounded_Zdiv (x y : Z) :
  'Zdiv x y ≤ ('x / 'y : Q) < 'Zdiv x y + 1.
Proof.
  rewrite Qround.Zdiv_Qdiv.
  split.
   now apply Qround.Qfloor_le.
  rewrite <-(rings.preserves_1 (f:=cast Z Q)).
  rewrite <-rings.preserves_plus.
  now apply Qround.Qlt_floor.
Qed.

Lemma Qpow_bounded_Zshiftl (x n : Z) : 
  'Zshiftl x n ≤ cast Z Q x * 2 ^ n < 'Zshiftl x n + 1.
Proof.
  destruct (total (≤) 0 n) as [En | En].
   rewrite Z.shiftl_mul_pow2 by trivial.
   rewrite inject_Z_mult.
   rewrite Qpower.Zpower_Qpower by trivial.
   split; try reflexivity.
   apply semirings.pos_plus_lt_compat_r.
   now apply (semirings.lt_0_1 (R:=Q)).
  rewrite Z.shiftl_div_pow2 by trivial.
  assert (('x * 2 ^ n : Q) = 'x / 'Zpower 2 (-n)).
   rewrite Qpower.Zpower_Qpower.
    rewrite <-Qpower.Qpower_opp, Zopp_involutive.
    reflexivity.
   now apply rings.flip_nonpos_opp in En.
  split.
   transitivity ('x / 'Zpower 2 (-n) : Q).
    now apply Qdiv_bounded_Zdiv.
   apply orders.eq_le. now symmetry.
  apply orders.le_lt_trans with ('x / 'Zpower 2 (-n) : Q).
   now apply orders.eq_le.
  now apply Qdiv_bounded_Zdiv.
Qed.

Lemma bigD_div_correct (x y : bigD) (k : Z) : Qball (2 ^ k) ('app_div x y k) ('x / 'y).
Proof.
  assert (∀ xm xe ym ye : Z, 
      ('xm * 2 ^ xe : Q) / ('ym * 2 ^ ye : Q) = ('xm * 2 ^ (-(k - 1) + xe - ye)) / 'ym * 2 ^ (k - 1)) as E1.
   intros.
   rewrite 2!int_pow_exp_plus by solve_propholds.
   rewrite dec_fields.dec_mult_inv_distr.
   rewrite 2!int_pow_opp.
   transitivity ('xm / 'ym * 2 ^ xe / 2 ^ ye * (2 ^ (k - 1) / 2 ^ (k - 1)) : Q); [ | ring].
   rewrite dec_mult_inverse by solve_propholds. ring.
  assert (∀ xm xe ym ye : Z, 
      'Zdiv (Zshiftl xm (-(k - 1) + xe - ye)) ym * 2 ^ (k - 1) - 2 ^ k  ≤ ('xm * 2 ^ xe) / ('ym * 2 ^ ye : Q)) as Pleft.
   clear x y.
   assert (∀ z : Q, z * 2 ^ (k - 1) - 2 ^ k = ((z - 1) - 1) * 2 ^ (k - 1)) as E2.
    intros.
    ms_setoid_replace k with ((k - 1) + 1) at 2 by ring.
    rewrite (int_pow_exp_plus (k - 1)) by solve_propholds.
    ring_simplify. apply sm_proper. now rewrite commutativity.
   intros. rewrite E1, E2.
   apply (order_preserving (.* _)).
   apply rings.flip_le_minus_l. 
   apply semirings.plus_le_compat_r; [easy | ].
   transitivity ('Zshiftl xm (-(k - 1) + xe - ye) / 'ym - 1 : Q).
    apply (order_preserving (+ -1)). now apply Qdiv_bounded_Zdiv.
   destruct (orders.le_or_lt 0 ym) as [E | E].
    apply rings.flip_le_minus_l. 
    apply semirings.plus_le_compat_r; [easy | ].
    apply (maps.order_preserving_flip_nonneg (.*.) (/ 'ym : Q)).
     apply dec_fields.nonneg_dec_mult_inv_compat.
     now apply semirings.preserves_nonneg.
    now apply Qpow_bounded_Zshiftl.
   transitivity (('Zshiftl xm (-(k - 1) + xe - ye) + 1) / 'ym : Q).
    rewrite rings.plus_mult_distr_r.
    apply semirings.plus_le_compat; [reflexivity | ].
    rewrite rings.mult_1_l.
    apply rings.flip_le_opp.
    rewrite rings.opp_involutive, dec_fields.dec_mult_inv_opp.
    apply dec_fields.flip_le_dec_mult_inv_l; [solve_propholds | ].
    rewrite <-rings.preserves_opp.
    apply semirings.preserves_ge_1.
    apply rings.flip_le_opp.
    rewrite rings.opp_involutive.
    now apply integers.le_iff_lt_plus_1.
   apply semirings.flip_nonpos_mult_r.
    apply dec_fields.nonpos_dec_mult_inv_compat.
    apply semirings.preserves_nonpos.
    now apply orders.lt_le.
   now apply orders.lt_le, Qpow_bounded_Zshiftl.
  assert (∀ xm xe ym ye : Z, 
      ('xm * 2 ^ xe) / ('ym * 2 ^ ye : Q) ≤ '(Zdiv (Zshiftl xm (-(k - 1) + xe - ye)) ym) * 2 ^ (k - 1) + 2 ^ k) as Pright.
   clear x y.
   assert (∀ z : Q, z * 2 ^ (k - 1) + 2 ^ k = ((z + 1) + 1) * 2 ^ (k - 1)) as E2.
    intros.
    ms_setoid_replace k with ((k - 1) + 1) at 2 by ring.
    rewrite (int_pow_exp_plus (k - 1)) by solve_propholds.
    ring_simplify. apply sm_proper. now apply commutativity.
   intros. rewrite E1, E2.
   apply (order_preserving (.* _)).
   transitivity ('Zshiftl xm (-(k - 1) + xe - ye) / 'ym + 1 : Q).
    2: now apply (order_preserving (+1)); apply orders.lt_le, Qdiv_bounded_Zdiv.
   destruct (orders.le_or_lt ym 0) as [E3 | E3].
    apply semirings.plus_le_compat_r; [easy | ].
    apply semirings.flip_nonpos_mult_r.
     apply dec_fields.nonpos_dec_mult_inv_compat.
     now apply semirings.preserves_nonpos.
    now apply Qpow_bounded_Zshiftl.
   transitivity (('Zshiftl xm (-(k - 1) + xe - ye) + 1) / ' ym : Q).
    apply (maps.order_preserving_flip_nonneg (.*.) (/ 'ym : Q)).
     apply dec_fields.nonneg_dec_mult_inv_compat.
     apply semirings.preserves_nonneg.
     now apply orders.lt_le.
    now apply orders.lt_le, Qpow_bounded_Zshiftl.
   rewrite rings.plus_mult_distr_r.
   apply semirings.plus_le_compat; [reflexivity | ].
   rewrite rings.mult_1_l.
   apply dec_fields.flip_le_dec_mult_inv_l; [solve_propholds | ].
   apply semirings.preserves_ge_1.
   now apply integers.lt_iff_plus_1_le in E3.
  unfold cast. rewrite 3!inject_bigD_Q_correct.
  destruct x as [xm xe], y as [ym ye]. simpl.
  unfold cast, inject_bigZ_Q, cast, "∘". simpl. BigZ.zify.
  apply in_Qball. split. apply Pleft. apply Pright.
Qed.

Instance inverse_Q_bigD: AppInverse inject_bigD_Q := λ x ε, 
  app_div ('Qnum x) ('(Qden x : Z)) (Qdlog2 ε).

Instance bigD_approx : AppApprox bigD := λ x k,
  BigZ.shiftl (mant x) (-('k - 1) + expo x) ▼ ('k - 1).

Lemma bigD_approx_correct (x : bigD) (k : Z) : Qball (2 ^ k) ('app_approx x k) ('x).
Proof.
  setoid_replace (app_approx x k) with (app_div x 1 k).
   setoid_replace ('x : Q) with ('x / '1 : Q).
    now apply bigD_div_correct.
   rewrite rings.preserves_1, dec_fields.dec_mult_inv_1.
   now rewrite rings.mult_1_r.
  unfold app_div, bigD_div.
  simpl. rewrite BigZ.div_1_r.
  setoid_replace (-('k - 1) + expo x - 0) with (-('k - 1) + expo x); [reflexivity | ].
  now rewrite rings.opp_0, rings.plus_0_r.
Qed.

Instance: DenseEmbedding inject_bigD_Q.
Proof.
  split; try apply _.
  intros [n d] ε.
  unfold app_inverse, inverse_Q_bigD.
  apply ball_weak_le with (2 ^ Qdlog2 ε)%Qpos.
   now apply (Qpos_dlog2_spec ε).
  simpl. rewrite Qmake_Qdiv.
  rewrite 2!(integers.to_ring_unique_alt inject_Z (inject_bigD_Q ∘ dy_inject ∘ BigZ.of_Z)).
  apply bigD_div_correct.
Qed.

Instance bigD_Zshiftl: ShiftL bigD Z := λ x n, x ≪ 'n.

Instance: Proper ((=) ==> (=) ==> (=)) bigD_Zshiftl.
Proof. unfold bigD_Zshiftl. solve_proper. Qed.

Instance: ShiftLSpec bigD Z bigD_Zshiftl.
Proof.
  split; try apply _; unfold shiftl, bigD_Zshiftl.
   intros x. rewrite rings.preserves_0. now apply shiftl_0.
  intros x n. rewrite rings.preserves_plus. now apply shiftl_S.
Qed.

(* 
  This function is more or less a copy of dy_pow, but uses [N] instead of [BigZ⁺] for the exponent. 
  An alternative definition would have been bigD_Npow x n = dy_pow x (N_to_BigZ_NonNeg n).
  However, then the exponent would be translated from [N] into [BigZ] and back again, due to the 
  definition of [BigZ.pow]. 
*) 
Instance bigD_Npow: Pow bigD N := λ x n, (mant x) ^ n ▼ 'n * expo x.

Instance: NatPowSpec bigD N bigD_Npow.
Proof.
  split; unfold "^", bigD_Npow, equiv, dy_equiv, DtoQ_slow.
    intros [xm xe] [ym ye] E1 e1 e2 E2. simpl in *.
    rewrite E2. clear e1 E2.
    rewrite 2!(preserves_nat_pow (f:=integers.integers_to_ring bigZ Q)).
    rewrite 2!(commutativity ('e2 : bigZ)).
    rewrite 2!int_pow_exp_mult.
    rewrite 2!(int_pow_nat_pow (f:=cast N bigZ)).
    rewrite <-2!nat_pow_base_mult.
    now rewrite E1.
   intros [xm xe]. simpl.
   rewrite rings.preserves_0, left_absorb.
   now rewrite nat_pow_0.
  intros [xm xe] n. simpl.
  rewrite nat_pow_S.
  rewrite rings.preserves_plus, rings.preserves_1.
  now rewrite distribute_r, left_identity.
Qed.

Instance: AppRationals bigD.
Proof.
  split; try apply _; intros.
    split; apply _.
   now apply bigD_div_correct.
  now apply bigD_approx_correct.
Qed.

Notation ARbigD := (AR (AQ:=bigD)).
