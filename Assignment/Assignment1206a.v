Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Import SetsNotation
       KleeneFix Sets_CPO
       SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

(************)
(** 习题：  *)
(************)

(** 请证明下面程序的性质。*)

Definition body_count (n: Z) (x: Z): SetMonad.M (ContinueOrBreak Z Z) :=
  choice
    (test (x < n);; continue (x + 1))
    (test (~ (x < n));; break x).

Definition count (n: Z): SetMonad.M Z :=
  repeat_break (body_count n) 0.

Theorem functional_correctness_count:
  forall n,
    0 < n ->
    Hoare (count n) (fun x => x = n).
Proof.
  intros.
  unfold count.
  apply (Hoare_repeat_break (body_count n) (fun x => x <= n)).
  + intros.
    unfold body_count.
    apply Hoare_choice.
    - apply Hoare_test_bind.
      intros.
      apply Hoare_ret.
      lia.
    - apply Hoare_test_bind.
      intros.
      apply Hoare_ret.
      lia.
  + lia.
Qed.



(************)
(** 习题：  *)
(************)

(** 请证明下面程序的性质。*)

Definition body_slow_div (n m: Z):
  Z * Z -> SetMonad.M (ContinueOrBreak (Z * Z) (Z * Z)) :=
  fun '(x, y) =>
    choice
      (test (x < n);; break (x, y))
      (test (~ (x < n));; continue (x - n, y + 1)).

Definition slow_div (n m: Z): SetMonad.M (Z * Z) :=
  repeat_break (body_slow_div n m) (m, 0).

Theorem functional_correctness_slow_div:
  forall n m,
    0 < n ->
    0 <= m ->
    Hoare (slow_div n m)
          (fun '(x, y) => x + n * y = m /\ 0 <= x < n).
Proof.
  intros.
  unfold slow_div.
  apply (Hoare_repeat_break (body_slow_div n m) (fun '(x, y) => x + n * y = m /\ x >= 0)).
  + unfold body_slow_div.
    intros.
    destruct a.
    apply (Hoare_choice).
    - apply Hoare_test_bind.
      intros.
      apply Hoare_ret.
      split.
      * lia.
      * lia.
    - apply Hoare_test_bind.
      intros.
      apply Hoare_ret.
      split.
      * lia.
      * lia.
  + split.
    - lia.
    - lia.
Qed.
       

    

    


