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

Inductive entry: Type :=
     | ptr0: node -> entry
     | keyval: key -> V -> entry
     | keychild: key -> node -> entry
with node: Type :=
     | nil: node
     | cons: entry -> X -> node -> node.
(* every list of keychilds begins with a ptr0 *)

Definition cursor: Type := list (node * nat). (* ancestors and index *)
Definition relation: Type := node * nat.      (* root and numRecords *)

Fixpoint max_nat (m : nat) (n : nat) : nat :=
  match m with
  | O => n
  | S m' => (match n with
             | O => m
             | S n' => S (max_nat m' n')
             end)
  end.

Fixpoint node_depth (n:node) : nat :=
  match n with
  | nil => O
  | cons e _ n' => max_nat (entry_depth e) (node_depth n')
  end
with entry_depth (e:entry) : nat :=
  match e with
  | ptr0 n => S (node_depth n)
  | keyval _ _ => S O
  | keychild _ n => S (node_depth n)
  end.

Fixpoint node_length (n:node) : nat :=
  match n with
  | nil => O
  | cons _ _ n' => S (node_length n')
  end.

Fixpoint nth_entry (i:nat) (n:node) : option entry :=
  match i with
  | O => match n with
         | nil => None
         | cons e _ _ => Some e
         end
  | S i' => match n with
           | nil => None
           | cons _ _ n' => nth_entry i' n'
            end
  end.

Fixpoint nth_child (i:nat) (n:node) : option node :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 n' => Some n'
              | keyval _ _ => None
              | keychild _ n' => Some n'
              end
  end.

Fixpoint nth_val (i:nat) (n:node) : option V :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 _ => None
              | keyval _ v => Some v
              | keychild _ _ => None
              end
  end.

Fixpoint nth_key (i:nat) (n:node) : option key :=
  match nth_entry i n with
  | None => None
  | Some e => match e with
              | ptr0 _ => None
              | keychild k _ => Some k
              | keyval k _ => Some k
              end
  end.

Fixpoint cursor_valid (c:cursor): Prop :=
  match c with
  | [] => True
  | (n,x)::c' => (le x (node_length n)) /\ cursor_valid c'
  end.
(* maybe I should add a few things:
- the very first (deepest in the list) node should be the "total" node
- if we have (n,4) in the cursor, the next node is the fourth child of n
- the head points to a value
 *)

Fixpoint cursor_valid_bool (c:cursor): bool :=
  match c with
  | [] => true
  | (n,x)::c' => (x <=? (node_length n))%nat && cursor_valid_bool c'
  end.

Definition empty_btree: node := nil.
Definition empty_cursor: cursor := [].
                      
Fixpoint get_value (c:cursor) : option V :=
  match c with
  | [] => None
  | (n,x)::c' => nth_val x n
  end.

Fixpoint move_to_first (c:cursor) (curr:node): cursor :=
  match curr with
  | nil => c
  | cons e _ n' => match e with
                   | ptr0 n => move_to_first ((curr,0%nat)::c) n
                   | keychild _ _ => c           (* should not happen *)
                   | keyval k v => ((curr,0%nat)::c)
                   end
  end.

Fixpoint move_to_next_partial (c:cursor) : cursor :=
  match c with
  | [] => []
  | (n,x)::c' => 
    match (x <=? ((node_length n) -1))%nat with
    | true => (n,S x)::c'
    | false => move_to_next_partial c'
    end
  end.

Definition move_to_next (c:cursor): cursor :=
  match (move_to_next_partial c) with
  | [] => c                    (* C program returns false here *)
  | (n,x)::c' => match nth_child x n with
                 | Some n' => move_to_first c n'
                 | None => c
                 end
  end.

Definition get_key (c:cursor): option key :=
  match c with
  | [] => None
  | (n,x)::c' => nth_key x n
  end.

Fixpoint numKeys (n:node) : nat :=
  match n with
  | nil => 0%nat
  | cons e _ n => numKeys n + match e with
                              | ptr0 _ => 0%nat
                              | keychild _ _ => 1%nat
                              | keyval _ _ => 1%nat
                              end
  end.

Fixpoint numRecords (n:node) : nat :=
  match n with
  | nil => 0%nat
  | cons e _ n => numRecords n + match e with
                                 | ptr0 n' => numRecords n'
                                 | keychild _ n' => numRecords n'
                                 | keyval _ _ => 1%nat
                                 end
  end.

Definition isLeaf (n:node) : bool :=
  match n with
  | nil => true                 (* can we have nil intern nodes? or do they have pr0 at least? *)
  | cons e _ n => match e with
                  | keyval _ _ => true
                  | _ => false
                  end
  end.

Fixpoint node_to_list (n:node) : list entry :=
  match n with
  | nil => []
  | cons e _ n' =>
    match e with
    | ptr0 n'' => node_to_list n'
    | keyval k v => (keyval k v)::node_to_list n'
    | keychild k c => (keychild k c)::node_to_list n'
    end
  end.

Definition node_to_ptr0 (n:node) : option node :=
  match n with
  | nil => None
  | cons e _ n' =>
    match e with
    | ptr0 n'' => Some n''
    | _ => None
    end
  end.

Fixpoint findChildIndex (n:node) (k:key): nat :=
  match n with
  | nil => 0%nat
  | cons e _ n' => match e with
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

Fixpoint getRootNode (c:cursor) : node :=
  match c with
  | [(n,x)] => n
  | (n,x)::c' => getRootNode c'
  | [] => nil
  end.

Definition getCurrNode (c:cursor) : node :=
  match c with
  | (n,x)::c' => n              (* Or n(x) ? *)
  | [] => nil
  end.

Definition getEntryIndex (c:cursor) : nat :=
  match c with
  | (n,x)::c' => x
  | [] => 0%nat
  end.

(**
    REPRESENTATIONS IN SEPARATION LOGIC
**)

Definition value_rep (v:V) (p:val):= (* this should change if we change the type of Values *)
  data_at Tsh tint (Vint (Int.repr v)) p.

Compute (reptype (Tunion _Child_or_Record noattr)). (* to represent the entry list *)

Fixpoint entry_rep (e:entry) (p:val): mpred := (* only for keychild and keyval *)
  match e with
  | ptr0 _ => emp
  | keyval k v =>
    field_at Tsh (Tstruct _Entry noattr) (DOT _key) (Vint(Int.repr k)) p *
    EX q1:reptype (nested_field_type (Tstruct _Entry noattr) [StructField _ptr]),
          EX q2:val,
                !!(JMeq q1 q2) &&
          field_at Tsh (Tstruct _Entry noattr) (DOT _ptr) q1 p * 
           value_rep v (field_address (Tunion _Child_or_Record noattr) [UnionField _record] q2)
  | keychild k c =>
    field_at Tsh (Tstruct _Entry noattr) (DOT _key) (Vint(Int.repr k)) p *
    EX p':val, (* field_at Tsh (Tstruct _Entry noattr) (DOT _ptr) p' p * *)
          btnode_rep c p'
  end
with btnode_rep (n:node) (p:val):mpred :=
       field_at Tsh (Tstruct _BtNode noattr) (DOT _numKeys) (Vint(Int.repr (Z.of_nat(numKeys n)))) p *
       field_at Tsh (Tstruct _BtNode noattr) (DOT _isLeaf) (Val.of_bool (isLeaf n)) p *
       EX p':val,
       field_at Tsh (Tstruct _BtNode noattr) (DOT _ptr0) p' p *
       match n with
       | cons e _ n' => match e with
                      | ptr0 n'' => btnode_rep n'' p'
                      | _ => !!(p'=nullval)
                      end
       | nil => !!(p'=nullval)
       end (* this could be replaced by matching node_to_ptr0 but then we can't find the decreasing argument *) *
       (* something with node_to_list and entry_rep *) emp.

Definition relation_rep (r:relation) (p:val):mpred :=
  match r with
  | (n,r) => EX p':val,
                   field_at Tsh (Tstruct _Relation noattr) (DOT _root) p' p *
                   btnode_rep n p' *
                   field_at Tsh (Tstruct _Relation noattr) (DOT _numRecords) (Vint(Int.repr(Z.of_nat r))) p
  end.

Definition uncurry {A B C} (f: A -> B -> C) (xy: A*B) : C :=
  f (fst xy) (snd xy).

Definition cursor_rep (c:cursor) (p:val):mpred :=
  EX prel:val, EX pcurr:val, EX ancestors:list(node * val),
  !!(map fst ancestors = map fst c) && (* or its reverse? *)
  field_at Tsh (Tstruct _Cursor noattr) (DOT _relation) prel p * (* relation rep? *)
  btnode_rep (getRootNode c) prel *
  field_at Tsh (Tstruct _Cursor noattr) (DOT _currNode) pcurr p *
  btnode_rep (getCurrNode c) pcurr * (* this is redundant with the previous btnode_rep ? *)
  field_at Tsh (Tstruct _Cursor noattr) (DOT _entryIndex) (Vint(Int.repr(Z.of_nat(getEntryIndex c)))) p *
  field_at Tsh (Tstruct _Cursor noattr) (DOT _isValid) (Val.of_bool (cursor_valid_bool c)) p *
  field_at Tsh (Tstruct _Cursor noattr) (DOT _level) (Vint(Int.repr(Zlength c))) p *
  field_at Tsh (Tstruct _Cursor noattr) (DOT _nextAncestorPointerIdx) (map (fun x => Vint(Int.repr(Z.of_nat(snd x)))) c) p * (* or its reverse? *)
  field_at Tsh (Tstruct _Cursor noattr) (DOT _ancestors) (map snd ancestors) p *
  iter_sepcon ancestors (uncurry btnode_rep).

(**
    FUNCTION SPECIFICATIONS
 **)

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool
  PRE [ _isLeaf OF tint ]       (* why tint and not tbool? *)
  PROP ()
  LOCAL (temp _isLeaf (Val.of_bool isLeaf))
  SEP ()
  POST [ tptr (Tstruct _BtNode noattr) ]
  EX p:val, PROP ()
  LOCAL (temp ret_temp p)
  SEP (btnode_rep nil p).

Definition RL_NewRelation_spec : ident * funspec :=
  DECLARE _RL_NewRelation
  WITH u:unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr (Tstruct _Relation noattr) ]
  EX p:val, PROP ()
  LOCAL(temp ret_temp p)
  SEP (relation_rep (empty_btree,0%nat) p).

Definition RL_NewCursor_spec : ident * funspec :=
  DECLARE _RL_NewCursor
  WITH r:relation, p:val
  PRE [ _relation OF tptr (Tstruct _Relation noattr) ]
  PROP ()
  LOCAL (temp _relation p)
  SEP (relation_rep r p)
  POST [ tptr (Tstruct _Cursor noattr) ]
  EX p':val, PROP ()
  LOCAL(temp ret_temp p')
  SEP (relation_rep r p * cursor_rep empty_cursor p').

(** 
    GPROG
 **)

Definition Gprog : funspecs :=
        ltac:(with_library prog [
                             createNewNode_spec; RL_NewRelation_spec; RL_NewCursor_spec
 ]).


(**
    FUNCTION BODIES PROOFS
 **)

Lemma body_createNewNode: semax_body Vprog Gprog f_createNewNode createNewNode_spec.
Proof.
start_function.
(* forward_call (Tstruct _BtNode noattr). *)
Admitted.

Lemma body_NewRelation: semax_body Vprog Gprog f_RL_NewRelation RL_NewRelation_spec.
Proof.
start_function.
forward_call(true).
Intros vret.
forward_if (PROP () LOCAL (temp _pRootNode vret) SEP (btnode_rep nil vret; emp)).
- rewrite prop_sepcon2. entailer!. admit.
- forward.
  entailer!. Exists (Vint(Int.repr 0)). entailer!.
  Exists nullval. Exists nullval. entailer!.
  rewrite prop_sepcon2. entailer!. admit.
-forward. entailer!.
- (* forward_call (Tstruct _Relation noattr). *) admit.
Admitted.
(* Some confusion between tuint and tulong *)


Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _relation p) SEP(relation_rep r p)).
- admit.
- forward. auto.
- subst p. admit.               (* how to use forward_call here? *)
- (* forward_call (Tstruct _Cursor noattr). *) (*tuint and tulong*)
  admit.
Admitted.