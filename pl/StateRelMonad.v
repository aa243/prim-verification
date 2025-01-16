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
       Monad
       MonadNotation.
Local Open Scope sets.
Local Open Scope Z.
Local Open Scope monad.

Module Monad.

Class Monad (M: Type -> Type): Type := {
  bind: forall {A B: Type}, M A -> (A -> M B) -> M B;
  ret: forall {A: Type}, A -> M A;
}.

End Monad.

Module StateRelMonad.
Definition M (Σ A: Type) : Type :=
  Σ -> A -> Σ -> Prop.
(** (s1, a, s2) ∈ p *)

Definition ret (Σ A: Type) (a0: A) : M Σ A :=
  fun s1 a s2 => a = a0 /\ s1 = s2.

Definition bind (Σ A B: Type) (f : M Σ A) (g : A -> M Σ B) : M Σ B :=
  fun s1 b s3 => exists s2 a, f s1 a s2 /\ g a s2 b s3.

End StateRelMonad.
Import SetMonadOperator1.
Module StateRelMonadOp.

#[export] Instance state_rel_monad (Σ: Type): Monad (StateRelMonad.M Σ) :=
{ ret := StateRelMonad.ret Σ;
    bind := StateRelMonad.bind Σ }.

Notation "x <- c1 ;; c2" := (bind c1 (fun x => c2))
  (at level 61, c1 at next level, right associativity).

Notation " x : T <- c1 ;; c2" :=(bind c1 (fun x : T => c2))
  (at level 61, c1 at next level, right associativity).

Notation "' pat <- c1 ;; c2" :=
  (bind c1 (fun x => match x with pat => c2 end))
  (at level 61, pat pattern, c1 at next level, right associativity).

Notation "e1 ;; e2" := (bind e1 (fun _: unit => e2))
  (at level 61, right associativity).

Definition choice {Σ A: Type} (f g: StateRelMonad.M Σ A): StateRelMonad.M Σ A :=
f ∪ g.

Definition any {Σ: Type} (A: Type): StateRelMonad.M Σ A :=
fun s1 a s2 => s1 = s2.

Definition test {Σ: Type} (P: Σ -> Prop): StateRelMonad.M Σ unit :=
fun s1 _ s2 => P s1 /\ s1 = s2.

Definition any_in_set {Σ A: Type} (P: A -> Prop): StateRelMonad.M Σ A :=
  fun s1 a s2 => P a /\ s1 = s2.

Inductive ContinueOrBreak (A B: Type): Type :=
| by_continue (a: A)
| by_break (b: B).

Arguments by_continue {_} {_} (_).
Arguments by_break {_} {_} (_).

Definition repeat_break_f
            {Σ A B: Type}
            (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
            (W: A -> StateRelMonad.M Σ B)
            (a: A): StateRelMonad.M Σ B :=
            x <- body a;;
            match x with
            | by_continue a' => W a'
            | by_break b => ret b
end.

Definition repeat_break
{Σ A B: Type}
(body: A -> StateRelMonad.M Σ (ContinueOrBreak A B)):
A -> StateRelMonad.M Σ B :=
Kleene_LFix (repeat_break_f body).

Definition continue {Σ A B: Type} (a: A):
StateRelMonad.M Σ (ContinueOrBreak A B) :=
ret (by_continue a).

Definition break {Σ A B: Type} (b: B):
StateRelMonad.M Σ (ContinueOrBreak A B) :=
ret (by_break b).

Definition Hoare {Σ A: Type} (P: Σ -> Prop) (c: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop): Prop :=
  forall σ1 a σ2, P σ1 -> c σ1 a σ2 -> Q a σ2.



(* Import StateRelMonadOp. *)

(* Module StateRelMonadOpTheorems. *)

Theorem  Hoare_bind {Σ A B: Type}:
forall (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (M: A -> Σ -> Prop)
(g: A -> StateRelMonad.M Σ B) (Q: B -> Σ -> Prop),
Hoare P f M ->
(forall a: A, Hoare (M a) (g a) Q) ->
Hoare P (bind f g) Q.
Proof.
  intros.
  unfold Hoare, bind; sets_unfold; simpl; unfold StateRelMonad.bind.
  intros σ1 b σ3 ? ?.
  destruct H2 as [a [σ2 [? ?]]].
  pose proof H _ _ _ H1 H2.
  pose proof H0 σ2 _ _ _ H4 H3.
  apply H5.
Qed.

Theorem Hoare_ret {Σ A: Type}:
  forall (a0: A) (P: A -> Σ -> Prop),
    Hoare (P a0) (ret a0) P.
Proof.
  intros.
  unfold Hoare, ret; sets_unfold; simpl; unfold StateRelMonad.ret.
  intros.
  destruct H0; subst; tauto.
Qed.

Theorem Hoare_choice {Σ A: Type}:
  forall (P: Σ -> Prop) (f g: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop),
    Hoare P f Q ->
    Hoare P g Q ->
    Hoare P (choice f g) Q.
Proof.
  intros.
  unfold Hoare, choice; sets_unfold; simpl.
  intros.
  destruct H2.
  + apply (H _ _ _ H1 H2).
  + apply (H0 _ _ _ H1 H2).
Qed.

Theorem Hoare_test_bind {Σ A: Type}:
  forall (P Q: Σ -> Prop) (f: StateRelMonad.M Σ A) R,
    Hoare (fun s => Q s /\ P s) f R ->
    Hoare P (test Q;; f) R.
Proof.
  intros.
  eapply Hoare_bind; [| intros x; apply H].
  unfold Hoare, test; sets_unfold; simpl.
  intros.
  destruct H1.
  subst σ2.
  tauto.
Qed.

Theorem Hoare_any {Σ: Type}: 
  forall (A: Type) (P: Σ -> Prop),
    Hoare P (any A) (fun _ => P).
Proof.
  intros.
  unfold Hoare, any; sets_unfold; simpl.
  intros.
  subst σ2.
  tauto.
Qed.

Theorem Hoare_conseq {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q1 Q2: A -> Σ -> Prop),
    (forall σ, P1 σ -> P2 σ) ->
    (forall a σ, Q2 a σ -> Q1 a σ) ->
    Hoare P2 f Q2 ->
    Hoare P1 f Q1.
Proof.
  intros.
  unfold Hoare; intros.
  apply H0.
  apply (H1 σ1 a σ2).
  + apply H; tauto.
  + tauto.
Qed.

Theorem Hoare_conseq_pre {Σ A: Type}:
  forall (P1 P2: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop),
    (forall σ, P1 σ -> P2 σ) ->
    Hoare P2 f Q ->
    Hoare P1 f Q.
Proof.
  intros.
  eapply Hoare_conseq; eauto.
Qed.

Theorem Hoare_conseq_post {Σ A: Type}:
  forall (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q1 Q2: A -> Σ -> Prop),
    (forall a σ, Q2 a σ -> Q1 a σ) ->
    Hoare P f Q2 ->
    Hoare P f Q1.
Proof.
  intros.
  eapply Hoare_conseq; eauto.
Qed.

Theorem Hoare_conjunct {Σ A: Type}:
  forall (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q1 Q2: A -> Σ -> Prop),
    Hoare P f Q1 ->
    Hoare P f Q2 ->
    Hoare P f (fun a σ => Q1 a σ /\ Q2 a σ).
Proof.
  intros.
  unfold Hoare; intros.
  split.
  + apply (H σ1 a σ2); tauto.
  + apply (H0 σ1 a σ2); tauto.
Qed.

Theorem Hoare_forall {Σ A: Type}:
  forall (X: Type) (P: Σ -> Prop) (f: StateRelMonad.M Σ A) (Q: X -> A -> Σ -> Prop),
    (forall x, Hoare P f (Q x)) ->
    Hoare P f (fun a s => forall x, Q x a s).
Proof.
  intros.
  unfold Hoare; intros.
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_pre_ex {Σ A: Type}:
  forall (X: Type) (P: X -> Σ -> Prop) (f: StateRelMonad.M Σ A) (Q: A -> Σ -> Prop),
    (forall x, Hoare (P x) f Q) ->
    Hoare (fun s => exists x, P x s) f Q.
Proof.
  intros.
  unfold Hoare; intros.
  destruct H0 as [x ?].
  apply (H x _ _ _ H0 H1).
Qed.

Theorem Hoare_ret' {Σ A: Type}:
  forall (P: Σ -> Prop) (Q: A -> Σ -> Prop) (a0: A),
    (forall s, P s -> Q a0 s) ->
    Hoare P (ret a0) Q.
Proof.
  intros.
  unfold Hoare, ret; simpl; sets_unfold; unfold StateRelMonad.ret.
  intros.
  destruct H1; subst.
  apply H. tauto.
Qed.

Theorem Hoare_repeat_break {A B Σ: Type}:
  forall (body: A -> StateRelMonad.M Σ (ContinueOrBreak A B))
         (P: A -> Σ -> Prop)
         (Q: B -> Σ -> Prop),
    (forall a, Hoare (P a) (body a) (fun x s => match x with
                                        | by_continue a => P a s
                                        | by_break b => Q b s
                                        end)) ->
    (forall a, Hoare (P a) (repeat_break body a) Q).
Proof.
  intros.
  unfold Hoare; sets_unfold.
  intros s1 b s2 ?.
  unfold repeat_break, Kleene_LFix; unfold_CPO_defs.
  intros [n ?].
  revert a s1 b s2 H0 H1.
  change (forall a, Hoare (P a) (Nat.iter n (repeat_break_f body) ∅ a) Q).
  induction n; intros; simpl.
  + unfold Hoare; sets_unfold; intros; tauto.
  + unfold repeat_break_f at 1.
    eapply Hoare_bind.
    - apply H.
    - intros [a0 | b0].
      * apply IHn.
      * apply Hoare_ret.
Qed.

(* End StateRelMonadOpTheorems. *)

End StateRelMonadOp.