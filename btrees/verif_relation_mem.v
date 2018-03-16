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

Definition key := Z.            (* unsigned long in C *)

Section BTrees.
Variable V : Type.
Variable b : nat.

Inductive entry: Type :=
     | ptr0: node -> entry
     | keyval: key -> V -> entry
     | keychild: key -> node -> entry
with node: Type :=
     | nil: node
     | cons: entry -> node -> node.
(* every list of keychilds begins with a ptr0 *)

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
  | cons e n' => max_nat (entry_depth e) (node_depth n')
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
  | cons _ n' => S (node_length n')
  end.

Definition cursor: Type := list (node * nat). (* ancestors and index *)

Fixpoint nth_entry (i:nat) (n:node) : option entry :=
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
- the very first node should be the total node
- if we have n,4, the the next node is the fourth child of n
- the head points to a value
 *)

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
  | cons e n' => match e with
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














Fixpoint node_to_list (n:node) : list entry :=
  match n with
  | nil => []
  | cons e n' =>
    match e with
    | ptr0 n'' => node_to_list n'
    | keyval k v => (keyval k v)::node_to_list n'
    | keychild k c => (keychild k c)::node_to_list n'
    end
  end.

Definition node_to_ptr0 (n:node) : option node :=
  match n with
  | nil => None
  | cons e n' =>
    match e with
    | ptr0 n'' => Some n''
    | _ => None
    end
  end.

Definition btnode_rep (n:node) (p:val) : mpred :=
  EX nvl: list entry, EX ptr0: option node, EX pptr0: val,
     !!(nvl = node_to_list n) && !!(ptr0 = node_to_ptr0 n) &&
     (* if ptr0 = Some, then btnode_rep ptr0 pptr0 *)
     malloc_token Tsh (Tstruct _BtNode noattr) p
     (* * field_at Tsh (Tstruct _BtNode noattr) [StructField _isLeaf] (if ptr0=None then false else true) p * *)
     (* field_at Tsh (Tstruct _BtNode noattr) [StructField _numKeys] (Zlength nvl) p * *)
     (* field_at Tsh (Tstruct _BtNode noattr) [StructField _ptr0] (ptr0) p * (* should be a val *) *)
     (* field_at Tsh (Tstruct _BtNode noattr) [StructField _entries] (nvl) p (* this isn't right *) *).

Definition value_rep (v:V) (p:val):mpred := emp. (* todo *)

Definition key_rep (k:key) (p:val):mpred := emp. (* todo *)

Definition entry_rep (e:entry) (p:val) : mpred :=
  match e with
  | ptr0 _ => emp
  | keyval k v => value_rep v p * key_rep k p
  | keychild k c => key_rep k p * btnode_rep c p
  end.
                    (* not p but the corresponding field *)