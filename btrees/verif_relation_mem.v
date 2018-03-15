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

Definition cursor: Type := list nat. (* ancestors index *)

Fixpoint nth_child (i:nat) (n:node) : option node :=
  match i with
  | O => match n with
         | nil => None
         | cons e _ => match e with
                       | ptr0 n' => Some n'
                       | keyval _ _ => None
                       | keychild _ n' => Some n'
                       end
         end
  | S i' => match n with
            | nil => None
            | cons _ n' => nth_child i' n'
            end
  end.

Fixpoint nth_val (i:nat) (n:node) : option V :=
  match i with
  | O => match n with
         | nil => None
         | cons e _ => match e with
                       | ptr0 _ => None
                       | keyval _ v => Some v
                       | keychild _ _ => None
                       end
         end
  | S i' => match n with
            | nil => None
            | cons _ n' => nth_val i' n'
            end
  end.

Fixpoint is_valid (c:cursor) (n:node):= (* cursor is reversed *)
  match c with
  | [] => match n with
          | nil => True
          | _ => False
          end
  | i::c' => match c' with
             | [] => match nth_val i n with
                     | Some _ => True
                     | None => False
                     end
             | _ => match nth_child i n with
                    | Some n' => is_valid c' n'
                    | None => False
                    end
             end
  end.

Definition empty_btree: node := nil.
Definition empty_cursor: cursor := [].

Inductive partial_cursor_valid : cursor -> node -> node -> Prop :=
| pcv_emp: forall n, partial_cursor_valid [] n n
| pcv_root: forall (i:nat) n n', le i (node_length n) ->
                      nth_child i n = Some n' ->
                      partial_cursor_valid [i] n' n
| pcv_cons: forall i c curr curr' n, partial_cursor_valid c curr n ->
                                     le i (node_length curr) -> 
                                     nth_child i curr = Some curr' ->
                                     partial_cursor_valid (i::c) curr' n.

Inductive cursor_valid : cursor -> node -> Prop :=
| valid_val: forall c curr n i v, partial_cursor_valid c curr n ->
                                  nth_val i curr = Some v ->
                                  cursor_valid c n.
                      
Inductive get_value : cursor -> node -> V -> Prop :=
| get: forall c curr n i v, partial_cursor_valid c curr n ->
                            nth_val i curr = Some v ->
                            get_value c n v.




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