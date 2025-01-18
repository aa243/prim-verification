Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Classes.RelationClasses.
From SetsClass Require Import SetsClass.
Import SetsNotation.
Local Open Scope sets_scope.
Require Import PL.StateRelMonad.
Import StateRelMonad.
Import Monad.MonadNotation.
Require Import SetsClass.SetsClass.
Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Psatz.
Require Import Coq.Classes.Morphisms.
Require Import Coq.Lists.List.
Require Import Coq.Sorting.Permutation.
Require Import PL.FixedPoint.
Require Import PL.Monad.
Local Open Scope monad.
Local Open Scope sets.
Import SetsNotation
       KleeneFix Sets_CPO
       Monad
       MonadNotation.
Import SetMonadHoare
       SetMonadOperator0
       SetMonadOperator1
       ListNotations
       MonadNotation.

Record PreGraph (Vertex Edge: Type) := {
  vertices : list Vertex;            (* 顶点的有限列表 *)
  edges : list Edge;                 (* 边的有限列表 *)
  src : Edge -> Vertex;              (* 边的起点 *)
  dst : Edge -> Vertex;              (* 边的终点 *)
  weight: Edge -> Z;                 (* 边的权重 *)
}.

Notation "pg '.(vertices)'" := (vertices _ _ pg) (at level 1).
Notation "pg '.(edges)'" := (edges _ _ pg) (at level 1).
Notation "pg '.(src)'" := (src _ _ pg) (at level 1).
Notation "pg '.(dst)'" := (dst _ _ pg) (at level 1).
Notation "pg '.(weight)'" := (weight _ _ pg) (at level 1).

Definition get_edges {V E: Type} (pg: PreGraph V E): list E :=
  pg.(edges).

Definition vvalid {V E: Type} (pg: PreGraph V E) : V -> Prop :=
    fun v => In v pg.(vertices).

Definition evalid {V E: Type} (pg: PreGraph V E) : E -> Prop :=
    fun e => In e pg.(edges).

Notation "pg '.(vvalid)'" := (vvalid  pg) (at level 1).
Notation "pg '.(evalid)'" := (evalid pg) (at level 1).

Definition is_legal_graph {V E: Type} (pg: PreGraph V E): Prop :=
  forall e, pg.(evalid) e -> (pg.(vvalid) (pg.(src) e) /\ pg.(vvalid) (pg.(dst) e)).

Record step_aux {V E: Type} (pg: PreGraph V E) (e: E) (x y: V): Prop :=
{
  step_evalid: pg.(evalid) e;
  step_src_valid: pg.(vvalid) x;
  step_dst_valid: pg.(vvalid) y;
  step_src: pg.(src) e = x;
  step_dst: pg.(dst) e = y;
}.

Definition step {V E: Type} (pg: PreGraph V E) (x y: V): Prop :=
  exists e, step_aux pg e x y \/ step_aux pg e y x.

Definition connected {V E: Type} (pg: PreGraph V E): V -> V -> Prop :=
  clos_refl_trans (step pg).

Lemma step_symmetric {V E: Type}:
  forall (pg: PreGraph V E) (x y: V),
    step pg x y -> step pg y x.
Proof.
  intros.
  unfold step in *.
  destruct H as [e ?].
  exists e.
  tauto.
Qed.


Lemma step_on_one_edge {V E: Type}:
  forall (pg: PreGraph V E) (e: E),
    is_legal_graph pg ->
    pg.(evalid) e -> 
    step pg (pg.(src) e) (pg.(dst) e).
Proof.
  intros.
  unfold step.
  exists e.
  left.
  unfold is_legal_graph in H.
  specialize (H e H0).
  destruct H.
  constructor; auto.
Qed.


Record subgraph {V E: Type} (pg1 pg2: PreGraph V E): Prop :=
{
  subgraph_legal: is_legal_graph pg1;
  biggraph_legal: is_legal_graph pg2;
  subgraph_vvalid: pg1.(vvalid) ⊆ pg2.(vvalid);
  subgraph_evalid: pg1.(evalid) ⊆ pg2.(evalid);
  subgraph_src: forall e, e ∈ pg1.(evalid) -> pg1.(src) e = pg2.(src) e;
  subgraph_dst: forall e, e ∈ pg1.(evalid) -> pg1.(dst) e = pg2.(dst) e;
}.

Definition list_to_set {V: Type} (l: list V): V -> Prop := 
  fun v => In v l.

Definition graph_connected {V E: Type} (pg: PreGraph V E): Prop := 
  is_legal_graph pg /\ (forall x y, pg.(vvalid) x -> pg.(vvalid) y -> connected pg x y).

Theorem connected_symmetric {V E: Type}:
  forall (pg: PreGraph V E) x y, connected pg x y -> connected pg y x.
Proof.
  unfold connected.
  intros.
  induction_1n H.
  + reflexivity.
  + assert (step pg x0 x).
    {
      unfold step in H0.
      unfold step.
      destruct H0 as [e ?].
      exists e.
      destruct H0.
      + right.
        destruct H0.
        split.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
      + left.
        destruct H0.
        split.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
        - tauto.
    }
  transitivity_n1 x0.
  * tauto.
  * tauto.
Qed.

Theorem connected_in_subgraph_then_connected_in_graph {V E: Type}:
  forall (subg pg: PreGraph V E) x y, subgraph subg pg -> connected subg x y -> connected pg x y.
Proof.
  intros.
  assert (step subg ⊆ step pg).
  { 
    destruct H.
    unfold step.
    sets_unfold.
    intros.
    destruct H as [e ?].
    exists e.
    destruct H.
    + left.
      destruct H.
      split.
      - sets_unfold in subgraph_evalid0.
        specialize (subgraph_evalid0 e).
        tauto. 
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a).
        tauto.
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a0).
        tauto.
      - specialize (subgraph_src0 e).
        pose proof subgraph_src0 step_evalid0.
        rewrite <- H.
        tauto.
      - specialize (subgraph_dst0 e).
        pose proof subgraph_dst0 step_evalid0.
        rewrite <- H.
        tauto.
    + right.
      destruct H.
      split.
      - sets_unfold in subgraph_evalid0.
        specialize (subgraph_evalid0 e).
        tauto. 
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a0).
        pose proof subgraph_vvalid0 step_src_valid0.
        tauto.
      - sets_unfold in subgraph_vvalid0.
        specialize (subgraph_vvalid0 a).
        pose proof subgraph_vvalid0 step_dst_valid0.
        tauto.
      - specialize (subgraph_src0 e).
        pose proof subgraph_src0 step_evalid0.
        rewrite <- H.
        tauto.
      - specialize (subgraph_dst0 e).
        pose proof subgraph_dst0 step_evalid0.
        rewrite <- H.
        tauto.
  }
  unfold connected.
  unfold connected in H0.
  induction_1n H0.
  + reflexivity.
  + specialize (H1 x x0).
    assert (step subg ⊆ step pg).
    { 
      destruct H.
      unfold step.
      sets_unfold.
      intros.
      destruct H as [e ?].
      exists e.
      destruct H.
      + left.
        destruct H.
        split.
        - sets_unfold in subgraph_evalid0.
          specialize (subgraph_evalid0 e).
          tauto. 
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a).
          tauto.
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a0).
          tauto.
        - specialize (subgraph_src0 e).
          pose proof subgraph_src0 step_evalid0.
          rewrite <- H.
          tauto.
        - specialize (subgraph_dst0 e).
          pose proof subgraph_dst0 step_evalid0.
          rewrite <- H.
          tauto.
      + right.
        destruct H.
        split.
        - sets_unfold in subgraph_evalid0.
          specialize (subgraph_evalid0 e).
          tauto. 
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a0).
          pose proof subgraph_vvalid0 step_src_valid0.
          tauto.
        - sets_unfold in subgraph_vvalid0.
          specialize (subgraph_vvalid0 a).
          pose proof subgraph_vvalid0 step_dst_valid0.
          tauto.
        - specialize (subgraph_src0 e).
          pose proof subgraph_src0 step_evalid0.
          rewrite <- H.
          tauto.
        - specialize (subgraph_dst0 e).
          pose proof subgraph_dst0 step_evalid0.
          rewrite <- H.
          tauto.
    }
    specialize (IHrt pg).
    pose proof IHrt H H3.
    pose proof H1 H2.
    transitivity x0; [ | tauto].
    transitivity_1n x0.
    * tauto.
    * reflexivity.
Qed.

Theorem connected_symmetric {V E: Type}:
 forall (pg: PreGraph V E) x y, connected pg x y -> connected pg y x.
Proof.
 unfold connected.
 intros.
 induction_1n H.
 + reflexivity.
 + assert (step pg x0 x).
  {
  unfold step in H0.
   unfold step.
   destruct H0 as [e ?].
  exists e.
  destruct H0.
  + right.
  destruct H0.
  split.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  + left.
  destruct H0.
  split.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  - tauto.
  }
 transitivity_n1 x0.
 * tauto.
 * tauto.
Qed.

Definition is_tree {V E: Type} (pg: PreGraph V E) (vl: list V) (el: list E): Prop := 
    length el + 1 = length vl /\
    graph_connected (Build_PreGraph V E vl el pg.(src) pg.(dst) pg.(weight)).

(**求列表和*)
Definition get_sum {V E: Type} (pg: PreGraph V E) (l: list E): Z :=
  fold_right Z.add 0%Z (map pg.(weight) l).

Definition is_spanning_tree {V E: Type} (pg: PreGraph V E) (vl: list V) (el: list E): Prop := 
  is_tree pg vl el /\ (list_to_set vl) == pg.(vvalid).

Definition is_minimal_spanning_tree {V E: Type} (pg: PreGraph V E) (vl: list V) (el: list E): Prop :=
  is_spanning_tree pg vl el /\ (forall vl' el', is_spanning_tree pg vl' el' -> (get_sum pg el <= get_sum pg el')%Z).

Theorem nonempty_finite_set_has_minimal: 
  forall (L: list Z) (A: Z -> Prop),
    (exists a, A a) -> 
    (forall a, A a -> In a L) -> 
    exists a, A a /\ (forall a', A a' -> a <= a')%Z.
Proof.
  induction L.
  + intros.
    destruct H as [a ?].
    specialize (H0 a).
    destruct H0; tauto.
  + intros.
    specialize (IHL A).
    Admitted.
    

Theorem finite_graph_has_finite_subgraphs {V E: Type}: 
  forall (pg: PreGraph V E), 
    exists subgl: list (PreGraph V E), (forall subg, In subg subgl <-> subgraph subg pg).
Proof.
  (* by induction *)
  Admitted.


Theorem spanning_tree_exists {V E: Type}:
  forall (pg: PreGraph V E), 
    graph_connected pg -> 
    exists vl el, is_spanning_tree pg vl el.
Proof.
  (* by induction. *)
  Admitted.

Theorem minimal_spanning_tree_exists {V E: Type}:
  forall (pg: PreGraph V E), 
    graph_connected pg ->
    exists vl el, is_minimal_spanning_tree pg vl el.
Proof.
  unfold is_minimal_spanning_tree.
  intros.
  pose proof (spanning_tree_exists pg H).
  pose proof (finite_graph_has_finite_subgraphs pg).
  destruct H1 as [subgl ?].
  pose proof (nonempty_finite_set_has_minimal (map (get_sum pg) (map get_edges subgl))).
  Admitted.

Record State (V E: Type) := 
{
  vertex_taken: list V;
  edge_taken: list E;
}.

Notation "s '.(vertex_taken)'" := (vertex_taken _ _ s) (at level 1).
Notation "s '.(edge_taken)'" := (edge_taken _ _ s) (at level 1).

Definition set_of_adjacent_edge_to_taken {V E: Type} (pg: PreGraph V E) (s: State V E): E -> Prop :=
  fun e => 
    pg.(evalid) e /\ 
    ((In (pg.(src) e) s.(vertex_taken) /\ ~ In (pg.(dst) e) s.(vertex_taken)) 
    \/ (In (pg.(dst) e) s.(vertex_taken) /\ ~ In (pg.(src) e) s.(vertex_taken))).

Definition set_of_the_edges_want_to_add {V E: Type} (pg: PreGraph V E) (s: State V E): E -> Prop :=
  fun e => set_of_adjacent_edge_to_taken pg s e /\ 
  forall e', set_of_adjacent_edge_to_taken pg s e' -> (pg.(weight) e <= pg.(weight) e')%Z.

Definition set_of_the_vertices_want_to_add {V E: Type} (pg: PreGraph V E) (s: State V E) (e: E): V -> Prop :=
  fun v =>  
  ((pg.(src) e = v /\ In (pg.(dst) e) s.(vertex_taken)) \/ (pg.(dst) e = v /\ In (pg.(src) e) s.(vertex_taken))).

Definition add_the_edge_and_the_vertex {V E: Type} (pg: PreGraph V E) (e: E) (v: V): StateRelMonad.M (State V E) unit :=
  fun s1 _ s2 => 
    s2.(vertex_taken) = v :: s1.(vertex_taken) /\
    s2.(edge_taken) = e :: s1.(edge_taken).

Definition get_any_edge_in_edge_candidates {V E: Type} (pg: PreGraph V E): StateRelMonad.M (State V E) E :=
  fun s1 e s2 => 
    e ∈ set_of_the_edges_want_to_add pg s1 /\ s1 = s2.

Definition get_any_vertex_in_vertex_candidates {V E: Type} (pg: PreGraph V E) (e: E): StateRelMonad.M (State V E) V :=
  fun s1 v s2 => 
    v ∈ set_of_the_vertices_want_to_add pg s1 e /\ s1 = s2.

Import StateRelMonadOp.
    
(**开始定义算法过程*)
Definition body_prim {V E: Type} (pg: PreGraph V E): 
                unit -> StateRelMonad.M (State V E) (ContinueOrBreak unit unit) :=
      (**s1 是初始状态， s2 是返回后的状态*)
      (* edges_candidates <- (fun s1 tmp s2 => tmp = set_of_the_edges_want_to_add pg s1 /\ s1 = s2);; *)
      fun _ => choice (test (fun s1 => list_to_set s1.(vertex_taken) == pg.(vvalid));;
              break tt)
              (test (fun s1 => ~ (list_to_set s1.(vertex_taken) == pg.(vvalid)));;
              e <- get_any_edge_in_edge_candidates pg;;
              v <- get_any_vertex_in_vertex_candidates pg e;;
              add_the_edge_and_the_vertex pg e v;;
              continue tt).

Definition prim {V E: Type} (pg: PreGraph V E): unit -> StateRelMonad.M (State V E) unit :=
  fun _ => repeat_break (body_prim pg) tt.

(* 不变量 *)
(* 永远有一棵最小生成树包含以选的 *)
Definition I1 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  exists vl el, is_minimal_spanning_tree pg vl el 
  /\ list_to_set s.(vertex_taken) ⊆ list_to_set vl /\ list_to_set s.(edge_taken) ⊆ list_to_set el.

(* 选的永远是一棵树 *)
Definition I2 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  is_tree pg s.(vertex_taken) s.(edge_taken).

(* 选了所有点 *)
Definition I3 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  list_to_set s.(vertex_taken) == pg.(vvalid).

Theorem Hoare_get_any_edge_in_edge_candidates {V E: Type}:
  forall (pg: PreGraph V E) (P: State V E -> Prop),
  Hoare P (get_any_edge_in_edge_candidates pg) (fun e s => set_of_the_edges_want_to_add pg s e /\ P s).
Proof.
  intros.
  unfold Hoare, get_any_edge_in_edge_candidates.
  intros.
  destruct H0.
  subst.
  tauto.
Qed.

Theorem Hoare_get_any_vertex_in_vertex_candidates {V E: Type}:
  forall (pg: PreGraph V E) (e: E) (P: State V E -> Prop),
  Hoare P (get_any_vertex_in_vertex_candidates pg e) (fun v s => set_of_the_vertices_want_to_add pg s e v /\ P s).
Proof.
  intros.
  unfold Hoare, get_any_vertex_in_vertex_candidates.
  intros.
  destruct H0.
  subst.
  tauto.
Qed.


Definition I4 {V E: Type} (pg: PreGraph V E) (s: State V E): Prop :=
  is_legal_graph (Build_PreGraph V E s.(vertex_taken) s.(edge_taken) pg.(src) pg.(dst) pg.(weight)).

Theorem keep_I4 {V E: Type} (pg: PreGraph V E):
  graph_connected pg -> 
  Hoare (fun s => I4 pg s) 
        (body_prim pg tt)
        (fun res (s: State V E) => 
            match res with
            | by_continue _ => I4 pg s
            | by_break _ => I4 pg s
            end).
Proof.
Admitted.

Theorem keep_chosen_graph_legal {V E: Type}:
  forall (pg: PreGraph V E) (σ1 σ2: State V E) (e: E) (v: V),
  graph_connected pg -> 
  set_of_the_edges_want_to_add pg σ1 e ->
  set_of_the_vertices_want_to_add pg σ1 e v ->
  σ2.(vertex_taken) = v :: σ1.(vertex_taken) ->
  σ2.(edge_taken) = e :: σ1.(edge_taken) ->
  is_legal_graph {|
    vertices := σ1.(vertex_taken);
    edges := σ1.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} ->
  is_legal_graph {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.
Proof.
Admitted.


Lemma vertices_candidate_is_connected {V E: Type}:
  (* v是candiate， u是任意一点，u和v是连通的。 *)
  forall (pg: PreGraph V E) (σ1 σ2: State V E) (e: E) (v: V) (u: V),
  graph_connected pg -> 
  set_of_the_edges_want_to_add pg σ1 e ->
  set_of_the_vertices_want_to_add pg σ1 e v ->
  σ2.(vertex_taken) = v :: σ1.(vertex_taken) ->
  σ2.(edge_taken) = e :: σ1.(edge_taken) ->
  is_tree pg σ1.(vertex_taken) σ1.(edge_taken) ->
  In u σ2.(vertex_taken) ->
  connected
  {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |} v u.
Proof.
  intros.
  unfold set_of_the_edges_want_to_add in H0.
  unfold graph_connected in H.
  destruct H as [H L].
  unfold connected.
  unfold set_of_the_edges_want_to_add in H0.
  destruct H0.
  clear H6.
  unfold set_of_adjacent_edge_to_taken in H0.
  destruct H0.
  unfold set_of_the_vertices_want_to_add in H1.
  unfold is_tree in H4.
  destruct H4.
  clear H4.
  unfold graph_connected in H7.
  assert (In v σ2.(vertex_taken)).
  { rewrite H2. simpl. tauto. }
  assert (In e σ2.(edge_taken)).
  { rewrite H3. simpl. tauto. }
  assert (pg.(src) = {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.(src) ).
  { reflexivity. }
  assert (pg.(dst) = {|
    vertices := σ2.(vertex_taken);
    edges := σ2.(edge_taken);
    src := pg.(src);
    dst := pg.(dst);
    weight := pg.(weight)
  |}.(dst) ). { reflexivity. }
  rewrite H2 in H5.
  simpl in H5.
  destruct H5.
  * rewrite H5; reflexivity.
  * destruct H7.
   destruct H1.
    - destruct H1.
      destruct H6; [ tauto | ].
      destruct H6 as [H6 M]. 
      assert (is_legal_graph
      {|
        vertices := σ2.(vertex_taken);
        edges := σ2.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}).
      { rewrite H3.
        unfold is_legal_graph in *.
        intros.
        change ({|
          vertices := σ2.(vertex_taken);
          edges := e :: σ1.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |}.(evalid) e0) with (In e0 (e :: σ1.(edge_taken))) in H13.
        simpl in H13.
        destruct H13.
        ++ subst e0.
            split.
            ** rewrite <- H3.
                rewrite <- H9.
                change ({|
                  vertices := σ2.(vertex_taken);
                  edges := σ2.(edge_taken);
                  src := pg.(src);
                  dst := pg.(dst);
                  weight := pg.(weight)
                |}.(vvalid) (pg.(src) e)) with (In (pg.(src) e) σ2.(vertex_taken)).
                rewrite H1.
                tauto.
            ** rewrite <- H3.
                rewrite <- H10.
                change ({|
                  vertices := σ2.(vertex_taken);
                  edges := σ2.(edge_taken);
                  src := pg.(src);
                  dst := pg.(dst);
                  weight := pg.(weight)
                |}.(vvalid) (pg.(dst) e)) with (In (pg.(dst) e) σ2.(vertex_taken)).
                rewrite H2.
                simpl; right.
                tauto.
        ++ split.
           ** rewrite <- H3.
              rewrite <- H9.
              change ({|
                vertices := σ2.(vertex_taken);
                edges := σ2.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(vvalid) (pg.(src) e0)) with (In (pg.(src) e0) σ2.(vertex_taken)).
              rewrite H2.
              simpl; right.
              specialize (H7 e0 H13).
              tauto.
            ** rewrite <- H3.
              rewrite <- H10.
              change ({|
                vertices := σ2.(vertex_taken);
                edges := σ2.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(vvalid) (pg.(dst) e0)) with (In (pg.(dst) e0) σ2.(vertex_taken)).
              rewrite H2.
              simpl; right.
              specialize (H7 e0 H13).
              tauto. }
      transitivity_1n (pg.(dst) e).
      + rewrite <- H1.
        rewrite H9, H10.
        apply (step_on_one_edge _ e); [ | apply H8].
        rewrite <- H10.
        rewrite <- H9.
        tauto.
      + specialize (H11 (pg.(dst) e) u H6 H5).
        change (clos_refl_trans
        (step
           {|
             vertices := σ2.(vertex_taken);
             edges := σ2.(edge_taken);
             src := pg.(src);
             dst := pg.(dst);
             weight := pg.(weight)
           |}) (pg.(dst) e) u) with (connected {|
             vertices := σ2.(vertex_taken);
             edges := σ2.(edge_taken);
             src := pg.(src);
             dst := pg.(dst);
             weight := pg.(weight)
            |} (pg.(dst) e) u).
          apply (connected_in_subgraph_then_connected_in_graph {|
            vertices := σ1.(vertex_taken);
            edges := σ1.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
          |} _ (pg.(dst) e) u); [ | apply H11].
          split; [ apply H7 | apply H13 | sets_unfold; rewrite H2; simpl | sets_unfold; rewrite H3; simpl | intros; reflexivity | intros; reflexivity].
          ++ intros.
            change ({|
              vertices := v :: σ1.(vertex_taken);
              edges := σ2.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(vvalid) a) with (In a (v :: σ1.(vertex_taken))).
            simpl; tauto.
          ++ intros.
            change ({|
              vertices := σ2.(vertex_taken);
              edges := e :: σ1.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(evalid) a) with (In a (e :: σ1.(edge_taken))).
            simpl; tauto.
    - destruct H1.
      destruct H6; [ | tauto ].
      destruct H6 as [H6 M]. 
      assert (is_legal_graph
      {|
        vertices := σ2.(vertex_taken);
        edges := σ2.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}).
      { rewrite H3.
      unfold is_legal_graph in *.
      intros.
      change ({|
        vertices := σ2.(vertex_taken);
        edges := e :: σ1.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}.(evalid) e0) with (In e0 (e :: σ1.(edge_taken))) in H13.
      simpl in H13.
      destruct H13.
      ++ subst e0.
          split.
          ** rewrite <- H3.
              rewrite <- H9.
              change ({|
                vertices := σ2.(vertex_taken);
                edges := σ2.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(vvalid) (pg.(src) e)) with (In (pg.(src) e) σ2.(vertex_taken)).
              rewrite H2.
              simpl; right.
              tauto.
          ** rewrite <- H3.
              rewrite <- H10.
              change ({|
                vertices := σ2.(vertex_taken);
                edges := σ2.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(vvalid) (pg.(dst) e)) with (In (pg.(dst) e) σ2.(vertex_taken)).
              rewrite H1.
              tauto.
              ++ split.
              ** rewrite <- H3.
                 rewrite <- H9.
                 change ({|
                   vertices := σ2.(vertex_taken);
                   edges := σ2.(edge_taken);
                   src := pg.(src);
                   dst := pg.(dst);
                   weight := pg.(weight)
                 |}.(vvalid) (pg.(src) e0)) with (In (pg.(src) e0) σ2.(vertex_taken)).
                 rewrite H2.
                 simpl; right.
                 specialize (H7 e0 H13).
                 tauto.
               ** rewrite <- H3.
                 rewrite <- H10.
                 change ({|
                   vertices := σ2.(vertex_taken);
                   edges := σ2.(edge_taken);
                   src := pg.(src);
                   dst := pg.(dst);
                   weight := pg.(weight)
                 |}.(vvalid) (pg.(dst) e0)) with (In (pg.(dst) e0) σ2.(vertex_taken)).
                 rewrite H2.
                 simpl; right.
                 specialize (H7 e0 H13).
                 tauto. }
      transitivity_1n (pg.(src) e).
      + rewrite <- H1.
        apply step_symmetric.
        rewrite H9, H10.
        apply (step_on_one_edge _ e); [ | apply H8 ].
        rewrite <- H10.
        rewrite <- H9.
        tauto.
      + specialize (H11 (pg.(src) e) u H6 H5).
        change (clos_refl_trans
        (step
          {|
            vertices := σ2.(vertex_taken);
            edges := σ2.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
          |}) (pg.(src) e) u) with (connected {|
            vertices := σ2.(vertex_taken);
            edges := σ2.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
            |} (pg.(src) e) u).
          apply (connected_in_subgraph_then_connected_in_graph {|
            vertices := σ1.(vertex_taken);
            edges := σ1.(edge_taken);
            src := pg.(src);
            dst := pg.(dst);
            weight := pg.(weight)
          |} _ (pg.(src) e) u); [ | apply H11].
          split; [ apply H7 | apply H13 | sets_unfold; rewrite H2; simpl | sets_unfold; rewrite H3; simpl | intros; reflexivity | intros; reflexivity].
          ++ intros.
            change ({|
              vertices := v :: σ1.(vertex_taken);
              edges := σ2.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(vvalid) a) with (In a (v :: σ1.(vertex_taken))).
            simpl; tauto.
          ++ intros.
            change ({|
              vertices := σ2.(vertex_taken);
              edges := e :: σ1.(edge_taken);
              src := pg.(src);
              dst := pg.(dst);
              weight := pg.(weight)
            |}.(evalid) a) with (In a (e :: σ1.(edge_taken))).
            simpl; tauto.
  
Qed.

Theorem Hoare_add_the_edge_and_the_vertex {V E: Type}:
  forall (pg: PreGraph V E) (e: E) (v: V),
  graph_connected pg ->
  Hoare
  (fun s : State V E =>
   set_of_the_vertices_want_to_add pg s e v /\
   set_of_the_edges_want_to_add pg s e /\
   ~ list_to_set s.(vertex_taken) == pg.(vvalid) /\
   is_tree pg s.(vertex_taken) s.(edge_taken))
  (add_the_edge_and_the_vertex pg e v)
  (fun _ s => is_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold Hoare, add_the_edge_and_the_vertex.
  intros; clear a.
  destruct H1.
  destruct H0.
  destruct H3.
  destruct H3.
  pose proof H5 as L.
  clear H5.
  destruct H4. 
  unfold is_tree in *.
  destruct H5.
  split.
  + rewrite H1, H2.
    simpl.
    rewrite H5.
    lia.
  + unfold graph_connected.
    split.
    **
    apply (keep_chosen_graph_legal pg σ1 σ2 e v); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold graph_connected in H6; tauto]. 
    ** intros.
       change ({|
        vertices := σ2.(vertex_taken);
        edges := σ2.(edge_taken);
        src := pg.(src);
        dst := pg.(dst);
        weight := pg.(weight)
      |}.(vvalid) x) with (In x σ2.(vertex_taken)) in H7.
        change ({|
          vertices := σ2.(vertex_taken);
          edges := σ2.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |}.(vvalid) y) with (In y σ2.(vertex_taken)) in H8.
        rewrite H1 in H7.
        rewrite H1 in H8.
        simpl in H7, H8.
        destruct H7, H8.
        ++ subst; reflexivity.
        ++ subst x.
            apply (vertices_candidate_is_connected pg σ1 σ2 e v y); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold is_tree; tauto | rewrite H1; simpl; right; tauto].
        ++ subst y.
          apply (connected_symmetric _ v x).
          apply (vertices_candidate_is_connected pg σ1 σ2 e v x); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold is_tree; tauto | rewrite H1; simpl; right; tauto].
        ++ destruct H6.
        apply (connected_in_subgraph_then_connected_in_graph {|
          vertices := σ1.(vertex_taken);
          edges := σ1.(edge_taken);
          src := pg.(src);
          dst := pg.(dst);
          weight := pg.(weight)
        |} _ x y).
          -- split; [ tauto | 
          apply (keep_chosen_graph_legal pg σ1 σ2 e v); [tauto | unfold set_of_the_edges_want_to_add; tauto | tauto | tauto | tauto | unfold graph_connected in H6; tauto]
          | sets_unfold; rewrite H1; simpl | sets_unfold; rewrite H2; simpl | intros | intros ].
            +++ intros.
              change ({|
                vertices := v :: σ1.(vertex_taken);
                edges := σ2.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(vvalid) a) with (In a (v :: σ1.(vertex_taken))).
              simpl; tauto.
            +++ intros.
              change ({|
                vertices := σ2.(vertex_taken);
                edges := e :: σ1.(edge_taken);
                src := pg.(src);
                dst := pg.(dst);
                weight := pg.(weight)
              |}.(evalid) a) with (In a (e :: σ1.(edge_taken))).
              simpl; tauto.
            +++ reflexivity.
            +++ reflexivity.
          -- specialize (H9 x y H7 H8).
            tauto.
Qed.

(* Lemma keep_I2_and_I4 {V E: Type} (pg: PreGraph V E):
graph_connected pg -> 
Hoare (fun s => I2 pg s /\ I4 pg s) 
      (body_prim pg tt)
      (fun res (s: State V E) => 
          match res with
          | by_continue _ => I2 pg s /\ I4 pg s
          | by_break _ => I2 pg s /\ I4 pg s
          end).
Proof.
  intros.
  unfold I2, body_prim.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret'.
    intros.
    tauto.
  + apply Hoare_test_bind.
    eapply Hoare_bind.
    * apply (Hoare_get_any_edge_in_edge_candidates pg _).
    * intros e.
      eapply Hoare_bind.
      ++ apply (Hoare_get_any_vertex_in_vertex_candidates pg e _).
      ++ intros v.
          eapply Hoare_bind; [ | intros; apply Hoare_ret'].
          +++ apply (Hoare_add_the_edge_and_the_vertex pg e v).
          +++ intros. 
              simpl in H0.
              tauto.
Qed. *)

Lemma keep_I2 {V E: Type} (pg: PreGraph V E):
    graph_connected pg -> 
    Hoare (fun s => I2 pg s) 
          (body_prim pg tt)
          (fun res (s: State V E) => 
              match res with
              | by_continue _ => I2 pg s
              | by_break _ => I2 pg s
              end).
Proof.
  intros.
  unfold I2, body_prim.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    intros.
    apply Hoare_ret'.
    intros.
    tauto.
  + apply Hoare_test_bind.
    eapply Hoare_bind.
    * apply (Hoare_get_any_edge_in_edge_candidates pg _).
    * intros e.
      eapply Hoare_bind.
      ++ apply (Hoare_get_any_vertex_in_vertex_candidates pg e _).
      ++ intros v.
          eapply Hoare_bind; [ | intros; apply Hoare_ret'].
          +++ apply (Hoare_add_the_edge_and_the_vertex pg e v).
          +++ intros. 
              simpl in H0.
              tauto.
Qed.

Lemma break_with_I3 {V E: Type} (pg: PreGraph V E):
  forall (pg: PreGraph V E),
  graph_connected pg ->
  Hoare (fun s => I2 pg s /\ I4 pg s)
        (body_prim pg tt)
        (fun res (s: State V E) =>
            match res with
            | by_continue _ => I2 pg s /\ I4 pg s
            | by_break _ => I3 pg s
            end).
Proof.
  intros.
  unfold body_prim.
  apply Hoare_choice.
  + apply Hoare_test_bind.
    unfold I3.
    apply Hoare_ret'.
    tauto.
  + apply Hoare_test_bind.
    unfold I3.
    eapply Hoare_bind; [ apply Hoare_get_any_edge_in_edge_candidates | ].
    intros e.
    eapply Hoare_bind; [ apply Hoare_get_any_vertex_in_vertex_candidates | ].
    intros v.
    eapply Hoare_bind; [ | intros; apply Hoare_ret'].
    * apply (Hoare_add_the_edge_and_the_vertex pg0 e v).
    * intros.
      simpl in H0.
      unfold I2.
      tauto.
Qed.

(* 设{x,y}是新选的边，x在已选的里，y不在。 如果{x,y}在原来的最小生成树中，什么也不用干
如果不在，那么要修改这个最小生成树，要加上{x,y}，删掉一条边。
先来陈述找到这条要删的边的算法。 *)

(*  假设通过这个算法找到要删的边叫{u,v}，
1、要证明，删除u，v后，任意一点k，只用删除完生成树的边，要么和u连通，要么和v连通
   证明思路：未知
2、要证明：加上{x,y}后，u,v连通了
  证明思路：这跟{u,v}的构造有关
            先证明在y与x的在原先最小生成树的路径中，存在某一个边{u,v}，u还在已经选的树里，但v就不在了
            {u,v}的构造就选成这个。
            那么v->y（由构造）， y->x, x->u（已经选的是一棵树）。*)

(* Theorem find_the_edge_want_to_delete {V E: Type} (pg: PreGraph V E) (s: State V E) (e: E):
Proof.
  xxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxxx
Qed. *)



(* Theorem the_edge_want_to_delete {V E: Type} (s: State V E) (x y: V) (pg: PreGraph V E):

Proof.
  
Qed. *)



Theorem keep_I1 {V E: Type} (s1 s2: State V E):
  forall (u: V) (pg: PreGraph V E),
        pg.(vvalid) u -> 
        graph_connected pg -> 
        Hoare (fun s => I1 pg s) 
        (body_prim pg tt)
        (fun res (s: State V E) => 
            match res with
            | by_continue _ => I1 pg s
            | by_break _ => I1 pg s
            end).
Proof.
Admitted.

Lemma initial_state {V E: Type} (s: State V E):
    forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    s.(vertex_taken) = u :: nil /\ s.(edge_taken) = nil -> I1 pg s /\ I2 pg s.
Proof.
  intros u.
  unfold I1, I2, is_tree.
  intros.
  destruct H1 as [? ?].
  split.
  + pose proof (minimal_spanning_tree_exists pg H0).
    destruct H3 as [vl [el ?]].
    exists vl, el.
    split; auto.
    split.
    - intros v ?.
      unfold is_minimal_spanning_tree in H3.
      unfold is_spanning_tree in H3.
      destruct H3 as [[? ?] _].
      unfold is_tree in H3.
      destruct H3 as [? _].
      rewrite H1 in H4.
      unfold list_to_set in H4.
      simpl in H4.
      destruct H4; [| tauto].
      subst.
      apply H5.
      apply H.
    - rewrite H2.
      unfold list_to_set.
      simpl.
      sets_unfold; tauto.
  + split.
    - rewrite H1, H2.
      unfold length.
      lia.
Admitted.

Theorem prim_find_tree_if_break_f {V E: Type}:
  forall (pg: PreGraph V E),
  graph_connected pg -> 
  Hoare (fun s0 => I2 pg s0 /\ I4 pg s0)
        (prim pg tt)
        (fun (_: unit) (s: State V E) => 
        I2 pg s /\ I4 pg s).
Proof.
  intros.
  unfold prim.
  apply (Hoare_repeat_break (body_prim pg) 
                            (fun (_: unit) (s0: State V E) => I2 pg s0 /\ I4 pg s0)
                            (fun (_: unit) (s: State V E) => 
                            I2 pg s /\ I4 pg s)).
  intros.
  apply (keep_I2_and_I4 pg ).
  apply H.
Qed.

Theorem prim_find_all_vertices_if_break_f {V E: Type}:
  forall (pg: PreGraph V E),
  graph_connected pg -> 
  Hoare (fun s0 => I2 pg s0 /\ I4 pg s0)
        (prim pg tt)
        (fun (_: unit) (s: State V E) => 
            I3 pg s).
Proof.
  intros.
  unfold prim.
  apply (Hoare_repeat_break (body_prim pg) 
                            (fun (_: unit) (s0: State V E) => I2 pg s0 /\ I4 pg s0)
                            (fun (_: unit) (s: State V E) => 
                              I3 pg s)).
  intros.
  apply (break_with_I3 pg ).
  apply H.
Qed.

Theorem prim_find_spanning_tree_if_break_f {V E: Type}:
  forall (pg: PreGraph V E),
    graph_connected pg -> 
    Hoare (fun s0 => I2 pg s0 /\ I4 pg s0)
          (prim pg tt)
          (fun (_: unit) (s: State V E) => 
              is_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold is_spanning_tree.
  pose proof (prim_find_tree_if_break_f pg H).
  pose proof (prim_find_all_vertices_if_break_f pg H).
  unfold I2 in H0,H1.
  unfold I3 in H1.
  unfold I2.
  unfold Hoare.
  unfold Hoare in H0, H1.
  intros.
  specialize (H0 σ1 a σ2).
  specialize (H1 σ1 a σ2).
  pose proof H0 H2 H3.
  pose proof H1 H2 H3.
  tauto.
Qed.

Lemma initial_state_to_I2 {V E: Type} (s: State V E):
    forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    s.(vertex_taken) = u :: nil /\ s.(edge_taken) = nil -> I2 pg s.
Proof.
  intros.
  unfold I2.
  unfold is_tree.
  destruct H1 as [? ?].
  rewrite H2.
  rewrite H1.
  simpl.
  split; [ lia | ].
  unfold graph_connected.
  split.
  + unfold is_legal_graph.
    intros.
    assert (~ {|
      vertices := [u];
      edges := [];
      src := pg.(src);
      dst := pg.(dst);
      weight := pg.(weight)
    |}.(evalid) e).
    {
      unfold evalid.
      tauto. 
    }
    tauto.
  +
    intros.
    unfold connected.
    assert (In x [u]).
    {
      apply H3.
    }
    assert (In y [u]).
    {
      apply H4. 
    }
    assert (x = u).
    {
      simpl in H5.
      destruct H5; [rewrite H5 ; reflexivity| tauto].
    }
    assert (y = u).
    {
      simpl in H6.
      destruct H6; [rewrite H6 ; reflexivity| tauto].
    }
    subst.
    reflexivity.
Qed.


Theorem prim_find_spanning_tree_if_break {V E: Type}:
  forall (u: V) (pg: PreGraph V E),
    pg.(vvalid) u ->
    graph_connected pg -> 
    Hoare (fun s0 => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)
          (prim pg tt)
          (fun (_: unit) (s: State V E) => 
              is_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
  intros.
  unfold Hoare.
  pose proof (prim_find_spanning_tree_if_break_f pg H0).
  unfold Hoare in H1.
  intros σ1 a σ2.
  specialize (H1 σ1 a σ2).
  pose proof (initial_state_to_I2 σ1 u pg).
  pose proof H2 H H0.
  intros.
  pose proof (H3 H4).
  pose proof (H1 H6 H5).
  tauto.
Qed.



Theorem prim_functional_correctness_foundation {V E: Type}: 
    forall (u: V) (pg: PreGraph V E),
        pg.(vvalid) u ->
        graph_connected pg -> 
        Hoare (fun s => I1 pg s)
              (prim pg tt)
              (fun (_: unit) (s: State V E) => 
              is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
Admitted.

Theorem prim_functional_correctness {V E: Type}:
    forall (u: V) (pg: PreGraph V E),
      pg.(vvalid) u ->
      graph_connected pg -> 
      Hoare (fun s0 => s0.(vertex_taken) = u :: nil /\ s0.(edge_taken) = nil)
            (prim pg tt)
            (fun (_: unit) (s: State V E) => 
                is_minimal_spanning_tree pg s.(vertex_taken) s.(edge_taken)).
Proof.
Admitted.


