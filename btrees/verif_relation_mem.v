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
     | keyval: key -> V -> X -> entry X
     | keychild: key -> node X -> entry X
with node (X:Type): Type :=
     | btnode: option (node X) -> listentry X -> X -> node X
with listentry (X:Type): Type :=
     | nil: listentry X
     | cons: entry X -> listentry X -> listentry X.

Definition cursor (X:Type): Type := list (node X * nat). (* ancestors and index *)
Definition relation (X:Type): Type := node X * nat * X.  (* root and numRecords *)

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
    btnode ptr0 le _ => max_nat (listentry_depth le)
                                (match ptr0 with
                                 | None => O
                                 | Some n' => S (node_depth n') end)
  end
with listentry_depth {X:Type} (le:listentry X) : nat :=
       match le with
       | nil => O
       | cons e le' => max_nat (entry_depth e) (listentry_depth le')
       end
with entry_depth {X:Type} (e:entry X) : nat :=
       match e with
       | keyval _ _ _ => S O
       | keychild _ n => S (node_depth n)
       end.                                                 

Fixpoint nth_entry_le {X:Type} (i:nat) (le:listentry X): option (entry X) :=
  match i with
  | O => match le with
         | nil => None
         | cons e _ => Some e
         end
  | S i' => match le with
            | nil => None
            | cons _ le' => nth_entry_le i' le'
            end
  end.                          (* USEFUL? *)

Fixpoint move_to_first {X:Type} (c:cursor X) (curr:node X): cursor X:=
  match curr with btnode ptr0 le _ =>
                  match ptr0 with
                  | Some n => move_to_first ((curr,0%nat)::c) n
                  | None => match le with
                            | nil => c (* possible? *)
                            | cons e le' => match e with
                                            | keyval _ _ _ => ((curr,0%nat)::c)
                                            | keychild _ _ => c (* not possible, we would have a ptr0 otherwise *)
                                            end
                            end
                  end
  end.

Fixpoint le_length {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => O
  | cons _ le' => S (le_length le')
  end.

Definition node_length {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le _ =>
               match ptr0 with
               | None => le_length le
               | Some _ => S (le_length le)
               end
  end.

Fixpoint move_to_next_partial {X:Type} (c:cursor X) : cursor X :=
  match c with
  | [] => []
  | (n,i)::c' =>
    match (i <=? (node_length n) -1 )%nat with
    | true => (n,S i)::c'
    | false => move_to_next_partial c'
    end
  end.

Fixpoint nth_node_le {X:Type} (i:nat) (le:listentry X): option (node X) :=
  match i with
  | O => match le with
         | nil => None
         | cons e _ => match e with
                       | keychild _ n => Some n
                       | keyval _ _ _ => None
                       end
         end
  | S i' => match le with
            | nil => None
            | cons _ le' => nth_node_le i' le'
            end
  end.

Definition nth_node {X:Type} (i:nat) (n:node X): option (node X) :=
  match n with btnode ptr0 le _ =>
               match ptr0 with
               | None => nth_node_le i le
               | Some n' => match i with
                            | O => Some n'
                            | S i' => nth_node_le i' le
                            end
               end
  end.

Definition move_to_next {X:Type} (c:cursor X): cursor X :=
  match (move_to_next_partial c) with
  | [] => c                     (* C program returns false here *)
  | (n,i)::c' => match nth_node i n with
                 | Some n' => move_to_first c n'
                 | None => c    (* possible at leaf nodes *)
                 end
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

Fixpoint numKeys_le {X:Type} (le:listentry X) : nat :=
  match le with
  | nil => 0%nat
  | cons e le' => S (numKeys_le le')
  end.

Definition numKeys {X:Type} (n:node X) : nat :=
  match n with btnode ptr0 le x => numKeys_le le end.

Definition isLeaf {X:Type} (n:node X) : bool :=
  match n with btnode ptr0 le w => match ptr0 with
                                   | None => true
                                   | Some _ => false end
  end.

Definition getval (n:node val): val :=
  match n with btnode _ _ x => x end.

Fixpoint le_to_list (le:listentry val) : list (val * (val + val)) :=
  match le with
  | nil => []
  | cons e le' =>
    (match e with
     | keychild k c => ((Vlong(Int64.repr k)),  inl (getval c))
     | keyval k v x => ((Vlong(Int64.repr k)),  inr x) (* ptr to the record?? *)
     end) :: le_to_list le'
  end.

Fixpoint entry_rep (e:entry val):=
  match e with
  | keychild _ n => match n with btnode _ _ x => btnode_rep n x end
  | keyval _ v x => value_rep v x
  end
with btnode_rep (n:node val) (p:val):mpred :=
  match n with btnode ptr0 le x =>
  !!(x=p) &&
  malloc_token Tsh tbtnode p *
  field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys n)))) p *
  match ptr0 with
  | None => field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool true) p *
            field_at Tsh tbtnode (DOT _ptr0) nullval p
  | Some n' => field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool false) p *
               match n' with btnode _ _ p' => field_at Tsh tbtnode (DOT _ptr0) p' p * btnode_rep n' p' end
  end *
  field_at Tsh tbtnode (DOT _entries) (le_to_list le) p *
  le_iter_sepcon le
  end
with le_iter_sepcon (le:listentry val):mpred :=
  match le with
  | nil => emp
  | cons e le' => entry_rep e * le_iter_sepcon le'
  end.

Definition relation_rep (r:relation val) (p:val):mpred :=
  match r with
  | (n,c,x) => !!(x=p) &&
    EX p':val,
          field_at Tsh trelation (DOT _root) p' p *
          btnode_rep n p' *
          field_at Tsh trelation (DOT _numRecords) (Vint(Int.repr(Z.of_nat c))) p *
          malloc_token Tsh trelation p
  end.

Definition getCurrVal (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,_)::_ => match n with btnode _ _ x => x end
  end.

Definition getEntryIndex {X:Type} (c:cursor X) : nat :=
  match c with
  | (n,i)::_ => i
  | [] => 0%nat
  end.

Fixpoint cursor_valid_bool {X:Type} (c:cursor X): bool :=
  match c with
  | [] => true
  | (b,i)::c' => match b with btnode ptr0 le x => (i <=? (numKeys_le le))%nat && cursor_valid_bool c' end
  end.                          (* might be incomplete *)


Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  malloc_token Tsh tcursor p *
  field_at Tsh tcursor (DOT _currNode) (getCurrVal c) p *
  match r with (n,c,x) => field_at Tsh tcursor (DOT _relation) x p end *
  field_at Tsh tcursor (DOT _entryIndex) (Vint(Int.repr(Z.of_nat(getEntryIndex c)))) p *
  field_at Tsh tcursor (DOT _isValid) (Val.of_bool (cursor_valid_bool c)) p *
  field_at Tsh tcursor (DOT _level) (Vint(Int.repr(Zlength c))) p *
  field_at Tsh tcursor (DOT _nextAncestorPointerIdx) (map (fun x => Vint(Int.repr(Z.of_nat(snd x)))) c) p * (* or its reverse? *)
  field_at Tsh tcursor (DOT _ancestors) (map getval (map fst c)) p.
(* what about the list length that can be shorter than the array? *)
(* also the index might be not exactly the same for intern nodes (no -1) *)

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