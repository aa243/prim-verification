(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[Nat.iter]_的性质。*)


Theorem iter_add:
  forall {A: Type} (n m: nat) (f: A -> A) (x: A),
    Nat.iter (n + m) f x = Nat.iter n f (Nat.iter m f x).
Proof.
  intros.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    rewrite IHn.
    reflexivity.
Qed.


(************)
(** 习题：  *)
(************)

(** 请证明下面关于_[Nat.iter]_的性质。*)

Theorem iter_mul:
  forall {A: Type} (n m: nat) (f: A -> A) (x: A),
    Nat.iter (n * m) f x = Nat.iter n (Nat.iter m f) x.
Proof.
  intros.
  induction n.
  + simpl.
    reflexivity.
  + simpl.
    rewrite iter_add.
    rewrite IHn.
    reflexivity.
Qed.

