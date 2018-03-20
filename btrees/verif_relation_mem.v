(** * verif_relation_mem.v: Correctness proof of relation_mem.c *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs. mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

(**
    BTREES FORMAL MODEL
**)

Section BTrees.
Definition key := Z.            (* unsigned long in C *)
Definition V:Type := Z.         (* I need some type for value_rep *)
Variable b : nat.
Variable X:Type.                (* val or unit *)

Inductive entry (X:Type): Type :=
     | ptr0: btree X -> entry X
     | keyval: key -> V -> entry X
     | keychild: key -> btree X -> entry X
with node (X:Type): Type :=
     | nil: node X
     | cons: entry X -> node X -> node X
with btree (X:Type): Type :=
     | tree: node X -> X -> btree X.
(* every list of keychilds begins with a ptr0 *)

Definition cursor (X:Type): Type := list (btree X * nat). (* ancestors and index *)
Definition relation (X:Type): Type := btree X * nat.      (* root and numRecords *)

Fixpoint max_nat (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => (match n with
             | O => m
             | S n' => S (max_nat m' n')
             end)
  end.

Fixpoint node_depth {X:Type} (n:node X) : nat :=
  match n with
  | nil => O
  | cons e n' => max_nat (entry_depth e) (node_depth n')
  end
with entry_depth {X:Type} (e:entry X) : nat :=
  match e with
  | ptr0 b => match b with tree n _ => S (node_depth n) end
  | keyval _ _ => S O
  | keychild _ b => match b with tree n _ => S (node_depth n) end
  end.

Definition brtee_depth {X:Type} (b:btree X) : nat :=
  match b with tree n _ => node_depth n end.

Fixpoint node_length {X:Type} (n:node X) : nat :=
  match n with
  | nil => O
  | cons _ n' => S (node_length n')
  end.

Definition btree_length {X:Type} (b:btree X) : nat :=
  match b with tree n _ => node_length n end.

Fixpoint nth_entry {X:Type} (i:nat) (n:node X) : option (entry X) :=
  match i with
  | O => match n with
         | nil => None
         | cons e _ => Some e
         end
  | S i' => match n with
           | nil => None
           | cons _ n' => nth_entry i' n'
            end
  end.

Fixpoint nth_child {X:Type} (i:nat) (n:node X) : option (node X) :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 b => match b with tree n' _ => Some n' end
              | keyval _ _ => None
              | keychild _ b => match b with tree n' _ => Some n' end
              end
  end.

Fixpoint nth_tree {X:Type} (i:nat) (n:node X) : option (btree X) :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 b => Some b
              | keyval _ _ => None
              | keychild _ b => Some b
              end
  end.

Fixpoint nth_value {X:Type} (i:nat) (n:node X) : option V :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 _ => None
              | keyval _ v => Some v
              | keychild _ _ => None
              end
  end.

Fixpoint nth_key {X:Type} (i:nat) (n:node X) : option key :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 _ => None
              | keychild k _ => Some k
              | keyval k _ => Some k
              end
  end.

Fixpoint cursor_valid {X:Type} (c:cursor X): Prop :=
  match c with
  | [] => True
  | (b,x)::c' => match b with tree n _ => (le x (node_length n)) /\ cursor_valid c' end
  end.
(* maybe I should add a few things:
- the very first (deepest in the list) node should be the "total" node
- if we have (n,4) in the cursor, the next node is the fourth child of n
- the head points to a value
 *)

Fixpoint cursor_valid_bool {X:Type} (c:cursor X): bool :=
  match c with
  | [] => true
  | (b,x)::c' => match b with tree n _ => (x <=? (node_length n))%nat && cursor_valid_bool c' end
  end.

Definition empty_btree: btree unit := tree unit (nil unit) tt.
Definition empty_cursor: cursor unit := [].
                      
Fixpoint get_value {X:Type} (c:cursor X) : option V :=
  match c with
  | [] => None
  | (b,x)::c' => match b with tree n _ => nth_value x n end
  end.

Fixpoint move_to_first {X:Type} (c:cursor X) (curr:btree X): cursor X:=
  match curr with tree n _ => match n with
  | nil => c
  | cons e n' => match e with
                 | ptr0 b => move_to_first ((curr,0%nat)::c) b
                 | keychild _ _ => c           (* should not happen *)
                 | keyval k v => ((curr,0%nat)::c)
                 end
  end end.

Fixpoint move_to_next_partial {X:Type} (c:cursor X) : cursor X :=
  match c with
  | [] => []
  | (b,x)::c' => 
    match (x <=? ((btree_length b) -1))%nat with
    | true => (b,S x)::c'
    | false => move_to_next_partial c'
    end
  end.

Definition move_to_next {X:Type} (c:cursor X): cursor X :=
  match (move_to_next_partial c) with
  | [] => c                    (* C program returns false here *)
  | (b,x)::c' => match b with tree n _ => match nth_tree x n with
                 | Some b' => move_to_first c b'
                 | None => c
                 end
  end end.

Definition get_key {X:Type} (c:cursor X): option key :=
  match c with
  | [] => None
  | (b,x)::c' => match b with tree n _ => nth_key x n end
  end.

Fixpoint numKeys {X:Type} (n:node X) : nat :=
  match n with
  | nil => 0%nat
  | cons e n => numKeys n + match e with
                            | ptr0 _ => 0%nat
                            | keychild _ _ => 1%nat
                            | keyval _ _ => 1%nat
                            end
  end.

Fixpoint numRecords {X:Type} (n:node X) : nat :=
  match n with
  | nil => 0%nat
  | cons e n => numRecords n + match e with
                               | ptr0 b => match b with tree n' _ => numRecords n' end
                               | keychild _ b => match b with tree n' _ => numRecords n' end
                               | keyval _ _ => 1%nat
                               end
  end.

Definition isLeaf {X:Type} (n:node X) : bool :=
  match n with
  | nil => true                 (* can we have nil intern nodes? or do they have pr0 at least? *)
  | cons e n => match e with
                | keyval _ _ => true
                | _ => false
                end
  end.

Fixpoint node_to_list {X:Type} (n:node X) : list (entry X) :=
  match n with
  | nil => []
  | cons e n' =>
    match e with
    | ptr0 n'' => node_to_list n'
    | keyval k v => (keyval X k v)::node_to_list n'
    | keychild k c => (keychild X k c)::node_to_list n'
    end
  end.

Definition node_to_ptr0 {X:Type} (n:node X) : option (btree X) :=
  match n with
  | nil => None
  | cons e n' =>
    match e with
    | ptr0 b => Some b
    | _ => None
    end
  end.

Fixpoint findChildIndex {X:Type} (n:node X) (k:key): nat :=
  match n with
  | nil => 0%nat
  | cons e n' => match e with
                 | ptr0 _ => findChildIndex n' k
                 | keychild k' c => match (k <=? k')%Z with
                                    | true => 0%nat
                                    | false => S (findChildIndex n' k)
                                    end
                 | keyval  k' v => match (k <=? k')%Z with
                                   | true => 0%nat
                                   | false => S (findChildIndex n' k)
                                   end
                 end
  end.

Fixpoint getRootNode {X:Type} (c:cursor X) : (node X) :=
  match c with
  | [(b,x)] => match b with tree n _ => n end
  | (n,x)::c' => getRootNode c'
  | [] => nil X
  end.

Definition getCurrNode {X:Type} (c:cursor X) : node X :=
  match c with
  | (b,x)::c' => match b with tree n _ => n end              (* Or n(x) ? *)
  | [] => nil X
  end.

Definition getEntryIndex {X:Type} (c:cursor X) : nat :=
  match c with
  | (n,x)::c' => x
  | [] => 0%nat
  end.

(**
    REPRESENTATIONS IN SEPARATION LOGIC
 **)

Definition tbtnode:=      Tstruct _BtNode noattr.
Definition tentry:=       Tstruct _Entry noattr.
Definition tchildrecord:= Tunion _Child_or_Record noattr.
Definition trelation:=    Tstruct _Relation noattr.
Definition tcursor:=      Tstruct _Cursor noattr.

Definition value_rep (v:V) (p:val):= (* this should change if we change the type of Values? *)
  data_at Tsh tint (Vint (Int.repr v)) p.

Compute (reptype tchildrecord). (* to represent the entry list in btnode_rep *)
Compute (reptype (nested_field_type tentry [StructField _ptr])).

(* Fixpoint entry_rep (e:entry) (p:val): mpred := (* only for keychild and keyval *) *)
(*   match e with *)
(*   | ptr0 _ => emp *)
(*   | keyval k v => *)
(*     field_at Tsh tentry (DOT _key) (Vlong(Int64.repr k)) p * (* Vlong?? *) *)
(*     EX q1:reptype (nested_field_type tentry [StructField _ptr]), *)
(*     EX q2:val, *)
(*           !!(JMeq q1 q2) && *)
(*           field_at Tsh tentry (DOT _ptr) q1 p *  *)
(*           value_rep v (field_address tchildrecord [UnionField _record] q2) *)
(*   | keychild k c => *)
(*     field_at Tsh tentry (DOT _key) (Vlong(Int64.repr k)) p * *)
(*     EX q1: reptype (nested_field_type tentry [StructField _ptr]), *)
(*     EX q2:val, *)
(*           !!(JMeq q1 q2) && *)
(*           field_at Tsh tentry (DOT _ptr) q1 p * *)
(*           btnode_rep c (field_address tchildrecord [UnionField _child] q2) *)
(*   end *)
(* with btnode_rep (n:node) (p:val):mpred := *)
(*        field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat(numKeys n)))) p * *)
(*        field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool (isLeaf n)) p * *)
(*        EX p':val, *)
(*        field_at Tsh tbtnode (DOT _ptr0) p' p * *)
(*        match n with *)
(*        | cons e _ n' => match e with *)
(*                       | ptr0 n'' => btnode_rep n'' p' *)
(*                       | _ => !!(p'=nullval) *)
(*                       end *)
(*        | nil => !!(p'=nullval) *)
(*        end (* this could be replaced by matching node_to_ptr0 but then we can't find the decreasing argument *) * *)
(*        (* something with node_to_list and entry_rep *) emp. *)

(* Definition relation_rep (r:relation) (p:val):mpred := *)
(*   match r with *)
(*   | (n,r) => EX p':val, *)
(*                    field_at Tsh trelation (DOT _root) p' p * *)
(*                    btnode_rep n p' * *)
(*                    field_at Tsh trelation (DOT _numRecords) (Vint(Int.repr(Z.of_nat r))) p *)
(*   end. *)

(* Definition uncurry {A B C} (f: A -> B -> C) (xy: A*B) : C := *)
(*   f (fst xy) (snd xy). *)

(* Definition cursor_rep (c:cursor) (p:val):mpred := *)
(*   EX prel:val, EX pcurr:val, EX ancestors:list(node * val), *)
(*   !!(map fst ancestors = map fst c) && (* or its reverse? *) *)
(*   field_at Tsh tcursor (DOT _relation) prel p * (* relation rep? *) *)
(*   btnode_rep (getRootNode c) prel * *)
(*   field_at Tsh tcursor (DOT _currNode) pcurr p * *)
(*   btnode_rep (getCurrNode c) pcurr * (* this is redundant with the previous btnode_rep ? *) *)
(*   field_at Tsh tcursor (DOT _entryIndex) (Vint(Int.repr(Z.of_nat(getEntryIndex c)))) p * *)
(*   field_at Tsh tcursor (DOT _isValid) (Val.of_bool (cursor_valid_bool c)) p * *)
(*   field_at Tsh tcursor (DOT _level) (Vint(Int.repr(Zlength c))) p * *)
(*   field_at Tsh tcursor (DOT _nextAncestorPointerIdx) (map (fun x => Vint(Int.repr(Z.of_nat(snd x)))) c) p * (* or its reverse? *) *)
(*   field_at Tsh tcursor (DOT _ancestors) (map snd ancestors) p * *)
(*   iter_sepcon ancestors (uncurry btnode_rep). *)

(* (** *)
(*     FUNCTION SPECIFICATIONS *)
(*  **) *)

(* Definition createNewNode_spec : ident * funspec := *)
(*   DECLARE _createNewNode *)
(*   WITH isLeaf:bool *)
(*   PRE [ _isLeaf OF tint ]       (* why tint and not tbool? *) *)
(*   PROP () *)
(*   LOCAL (temp _isLeaf (Val.of_bool isLeaf)) *)
(*   SEP () *)
(*   POST [ tptr tbtnode ] *)
(*   EX p:val, PROP () *)
(*   LOCAL (temp ret_temp p) *)
(*   SEP (btnode_rep nil p). *)

(* Definition RL_NewRelation_spec : ident * funspec := *)
(*   DECLARE _RL_NewRelation *)
(*   WITH u:unit *)
(*   PRE [ ] *)
(*   PROP () *)
(*   LOCAL () *)
(*   SEP () *)
(*   POST [ tptr trelation ] *)
(*   EX p:val, PROP () *)
(*   LOCAL(temp ret_temp p) *)
(*   SEP (relation_rep (empty_btree,0%nat) p). *)

(* Definition RL_NewCursor_spec : ident * funspec := *)
(*   DECLARE _RL_NewCursor *)
(*   WITH r:relation, p:val *)
(*   PRE [ _relation OF tptr trelation ] *)
(*   PROP () *)
(*   LOCAL (temp _relation p) *)
(*   SEP (relation_rep r p) *)
(*   POST [ tptr tcursor ] *)
(*   EX p':val, PROP () *)
(*   LOCAL(temp ret_temp p') *)
(*   SEP (relation_rep r p * cursor_rep empty_cursor p'). *)

(* (**  *)
(*     GPROG *)
(*  **) *)

(* Definition Gprog : funspecs := *)
(*         ltac:(with_library prog [ *)
(*                              createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec *)
(*  ]). *)


(* (** *)
(*     FUNCTION BODIES PROOFS *)
(*  **) *)

(* Lemma body_createNewNode: semax_body Vprog Gprog f_createNewNode createNewNode_spec. *)
(* Proof. *)
(* start_function. *)
(* (* forward_call (Tstruct _BtNode noattr). *) *)
(* Admitted. *)

(* Lemma body_NewRelation: semax_body Vprog Gprog f_RL_NewRelation RL_NewRelation_spec. *)
(* Proof. *)
(* start_function. *)
(* forward_call(true). *)
(* Intros vret. *)
(* forward_if (PROP () LOCAL (temp _pRootNode vret) SEP (btnode_rep nil vret; emp)). *)
(* - rewrite prop_sepcon2. entailer!. admit. *)
(* - forward. *)
(*   entailer!. Exists (Vint(Int.repr 0)). entailer!. *)
(*   Exists nullval. Exists nullval. entailer!. *)
(*   rewrite prop_sepcon2. entailer!. admit. *)
(* -forward. entailer!. *)
(* - (* forward_call (Tstruct _Relation noattr). *) admit. *)
(* Admitted. *)
(* (* Some confusion between tuint and tulong *) *)


(* Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec. *)
(* Proof. *)
(* start_function. *)
(* forward_if (PROP() LOCAL(temp _relation p) SEP(relation_rep r p)). *)
(* - admit. *)
(* - forward. auto. *)
(* - subst p. admit.               (* how to use forward_call here? *) *)
(* - (* forward_call (Tstruct _Cursor noattr). *) (*tuint and tulong*) *)
(*   admit. *)
(* Admitted. *)