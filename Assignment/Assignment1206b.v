Require Import Coq.Lists.List.
Import ListNotations.

(************)
(** 习题：  *)
(************)

(** 下面定义的_[suffixes]_函数计算了一个列表的所有后缀。*)

Fixpoint suffixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l' => l :: suffixes l'
  end.

(** 例如 
   
        suffixes []           = [ [] ]
        suffixes [1]          = [ [1]; [] ]
        suffixes [1; 2]       = [ [1; 2]; [2]; [] ]
        suffixes [1; 2; 3; 4] = [ [1; 2; 3; 4];
                                  [2; 3; 4]   ;
                                  [3; 4]      ;
                                  [4]         ;
                                  []          ]
      
    接下去，请分三步证明，_[suffixes l]_中的确实是_[l]_的全部后缀。*)

Lemma self_in_suffixes:
  forall A (l: list A), In l (suffixes l).
Proof.
  induction l.
  + simpl.
    tauto.
  + simpl.
    tauto.
Qed.

Theorem in_suffixes:
  forall A (l1 l2: list A),
    In l2 (suffixes (l1 ++ l2)).
Proof.
  induction l1.
  + simpl.
    apply self_in_suffixes.
  + simpl.
    intros l2.
    specialize (IHl1 l2).
    tauto.
Qed.

Theorem in_suffixes_inv:
  forall A (l2 l: list A),
    In l2 (suffixes l) ->
    exists l1, l1 ++ l2 = l.
Proof.
  intros.
  induction l.
  + simpl in H.
    destruct H.
    - exists [].
      simpl.
      rewrite H.
      reflexivity.
    - contradiction.
  + simpl in H.
    destruct H.
    - rewrite H.
      exists [].
      simpl.
      reflexivity.
    - apply IHl in H as H0.
      destruct H0 as [l1 H0].
      exists (a :: l1).
      simpl.
      rewrite H0.
      reflexivity.
Qed.


(************)
(** 习题：  *)
(************)

(** 下面定义的_[prefixes]_函数计算了一个列表的所有前缀。*)

Fixpoint prefixes {A: Type} (l: list A): list (list A) :=
  match l with
  | nil => [nil]
  | a :: l0 => nil :: (map (cons a) (prefixes l0))
  end.

(** 例如：
   
        prefixes [1; 2]    = [ []     ;
                               [1]    ;
                               [1; 2] ] 
   
        prefixes [0; 1; 2] = [] ::
                             map (cons 0 (prefixes [1; 2]))
                           = [] ::
                             [ 0 :: []     ;
                               0 :: [1]    ;
                               0 :: [1; 2] ]
                           = [ []        ;
                               [0]       ;
                               [0; 1]    ;
                               [0; 1; 2] ]
      
    接下去，请分三步证明，_[prefixes l]_中的确实是_[l]_的全部前缀。*)

Lemma nil_in_prefixes:
  forall A (l: list A), In nil (prefixes l).
Proof.
  induction l.
  + simpl.
    tauto.
  + simpl.
    tauto.
Qed.


(* Lemma map: .
Proof.
  
Qed. *)


Theorem in_prefixes:
  forall A (l1 l2: list A),
    In l1 (prefixes (l1 ++ l2)).
Proof.
  induction l1.
  + simpl.
    apply nil_in_prefixes.
  + simpl.
    intros l2.
    specialize (IHl1 l2).
    right.
    pose proof (in_map (cons a) (prefixes (l1 ++ l2)) l1).
    apply H.
    apply IHl1.
Qed.


Theorem in_prefixes_inv:
  forall A (l1 l: list A),
    In l1 (prefixes l) ->
    exists l2, l1 ++ l2 = l.
Proof.
  induction l1.
  + simpl.
    intros.
    exists l.
    reflexivity.
  + simpl.
    induction l.
    - intros.
      simpl in H.
      destruct H.
      * discriminate H.
      * tauto.
    - intros.
      specialize (IHl1 l).
      destruct IHl1.
      * simpl in H.
        destruct H.
        -- discriminate H.
        -- pose proof (in_map_iff (cons a0) (prefixes l) ( a::l1)).
          apply H0 in H.
          destruct H as [x H1].
          destruct H1.
          injection H.
          intros.
          rewrite <- H2.
          apply H1.
      * exists x.
        rewrite H0.
        simpl in H.
        destruct H.
        -- discriminate H.
        -- pose proof (in_map_iff (cons a0) (prefixes l) ( a::l1)).
        apply H1 in H.
        destruct H as [x0 H2].
        destruct H2.
        injection H.
        intros.
        rewrite H4.
        reflexivity.
Qed.
    


    


