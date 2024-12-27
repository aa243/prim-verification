Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import PL.SimpleProofsAndDefs.
Local Open Scope Z.

(************)
(** 习题：  *)
(************)

(** 我们可以使用乘法运算定义“正负号不同”这个二元谓词。请基于这一定义完成相关性质的Coq证
    明。*)

Definition opposite_sgn (x y: Z): Prop := x * y < 0.

Fact opposite_sgn_plus_2: forall x,
  opposite_sgn (x + 2) x ->
  x = -1.
Proof.
  unfold opposite_sgn.
  intros.
  nia.
Qed.

Fact opposite_sgn_odds: forall x,
  opposite_sgn (square x) x ->
  x < 0.
Proof.
  unfold opposite_sgn, square.
  intros.
  nia.
Qed.


(************)
(** 习题：  *)
(************)

(** 下面定义的谓词_[quad_nonneg a b c]_表示：以_[a]_、_[b]_、_[c]_为系数的二次式在
    自变量去一切整数的时候都恒为非负。请基于这一定义完成相关性质的Coq证明。*)

Definition quad_nonneg (a b c: Z): Prop :=
  forall x: Z, a * x * x + b * x + c >= 0.

Lemma scale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg a b c ->
  quad_nonneg (k * a) (k * b) (k * c).
Proof.
  unfold quad_nonneg.
  intros.
  pose proof H0 x as H1.
  assert (k * (a * x * x + b * x + c) >= k * 0).
  {
     nia. 
  }
  nia.
Qed.

Lemma descale_quad_nonneg: forall a b c k: Z,
  k > 0 ->
  quad_nonneg (k * a) (k * b) (k * c) ->
  quad_nonneg a b c.
Proof.
  unfold quad_nonneg.
  intros.
  pose proof H0 x as H1.
  nia.
Qed.

Lemma plus_quad_nonneg: forall a1 b1 c1 a2 b2 c2: Z,
  quad_nonneg a1 b1 c1 ->
  quad_nonneg a2 b2 c2 ->
  quad_nonneg (a1 + a2) (b1 + b2) (c1 + c2).
Proof.
  unfold quad_nonneg.
  intros.
  pose proof H x as H1.
  pose proof H0 x as H2.
  lia.
Qed.

(** 我们知道，如果二次式的二次项系数为正且判别式不为正，那么这个二次式在自变量取遍一切
    实数的时候都恒为正。相应的性质在自变量取遍一切整数的时候自然也成立。请证明这一结
    论。【选做】*)

Lemma square_nonneg: forall x: Z,
  x * x >= 0.
Proof.
  nia.
Qed.

Lemma plus_quad_discriminant: forall a b c,
  a > 0 ->
  b * b - 4 * a * c <= 0 ->
  quad_nonneg a b c.
Proof.
  unfold quad_nonneg.
  intros.
  pose proof square_nonneg (2 * a * x + b) as H1.
  assert (4 * a * a * x * x + 4 * a * b * x + b * b >= 0).
  {
    lia.
  }
  nia.
Qed.
  

(** 然而，判别式不为正并不是_[quad_nonneg]_的必要条件。下面命题是一个简单的反例。*)

Example quad_nonneg_1_1_0: quad_nonneg 1 1 0.
Proof.
  unfold quad_nonneg.
  nia.
Qed.


(************)
(** 习题：  *)
(************)

(** 请证明下面命题。*)

Fact shift_up1_eq: forall f,
  shift_up1 f = func_plus f (fun x => 1).
Proof.
  unfold shift_up1, func_plus.
  reflexivity.
Qed.



(************)
(** 习题：  *)
(************)

(** 请证明常值函数都是单调的。*)

Lemma const_mono: forall a: Z,
  mono (fun x => a).
Proof.
  unfold mono.
  lia.
Qed.


(************)
(** 习题：  *)
(************)

(** 请证明函数加法能保持单调性。*)

Lemma mono_func_plus: forall f g,
  mono f ->
  mono g ->
  mono (func_plus f g).
Proof.
  unfold mono, func_plus.
  intros.
  specialize (H n m H1).
  pose proof H0 n m as H3.
  lia.
Qed.



(************)
(** 习题：  *)
(************)

(** 请在Coq中证明下面关于结合律的性质。*)

Definition power2 (f: Z -> Z -> Z) (x: Z): Z :=
  f x x.

Definition power4 (f: Z -> Z -> Z) (x: Z): Z :=
  f x (f x (f x x)).

Fact power2_power2: forall f a,
  assoc f ->
  power2 f (power2 f a) = power4 f a.
Proof.
  unfold assoc, power2, power4.
  intros.
  pose proof H a a (f a a) as H1.
  rewrite H1.
  reflexivity.
Qed.




