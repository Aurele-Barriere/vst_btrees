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

Definition Fanout := 15%nat.
Definition MaxTreeDepth := 20%nat.

Definition key := Z.            (* unsigned long in C *)
Definition V:Type := Z.         (* I need some type for value_rep *)
Variable b : nat.
Variable X:Type.                (* val or unit *)

Inductive entry (X:Type): Type :=
     | keyval: key -> V -> X -> entry X
     | keychild: key -> node X -> entry X
with node (X:Type): Type :=
     | btnode: option (node X) -> listentry X -> bool -> X -> node X
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
    btnode ptr0 le _ _ => max_nat (listentry_depth le)
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
  match curr with btnode ptr0 le _ _ =>
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
  match n with btnode ptr0 le _ _ =>
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
  match n with btnode ptr0 le _ _ =>
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
  match n with btnode ptr0 le _ x => numKeys_le le end.

Definition isLeaf {X:Type} (n:node X) : bool :=
  match n with btnode ptr0 le b w => b end.

Definition getval (n:node val): val :=
  match n with btnode _ _ _ x => x end.

Fixpoint le_to_list (le:listentry val) : list (val * (val + val)) :=
  match le with
  | nil => []
  | cons e le' =>
    (match e with
     | keychild k c => ((Vlong(Int64.repr k)),  inl (getval c))
     | keyval k v x => ((Vlong(Int64.repr k)),  inr x) (* ptr to the record?? *)
     end) :: le_to_list le'
  end.

Definition le_to_list_complete (le:listentry val):=
  le_to_list le ++ list_repeat (Fanout - numKeys_le le) (Vundef, inl Vundef).
                        
Fixpoint entry_rep (e:entry val):=
  match e with
  | keychild _ n => match n with btnode _ _ _ x => btnode_rep n x end
  | keyval _ v x => value_rep v x
  end
with btnode_rep (n:node val) (p:val):mpred :=
  match n with btnode ptr0 le b x =>
  !!(x=p) &&
  malloc_token Tsh tbtnode p *
  field_at Tsh tbtnode (DOT _numKeys) (Vint(Int.repr (Z.of_nat (numKeys n)))) p *
  field_at Tsh tbtnode (DOT _isLeaf) (Val.of_bool b) p *
  match ptr0 with
  | None => field_at Tsh tbtnode (DOT _ptr0) nullval p
  | Some n' => match n' with btnode _ _ _ p' => field_at Tsh tbtnode (DOT _ptr0) p' p * btnode_rep n' p' end
  end *
  field_at Tsh tbtnode (DOT _entries) (le_to_list_complete le) p *
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
          field_at Tsh trelation (DOT _numRecords) (Vlong(Int64.repr(Z.of_nat c))) p * (* long?int? *)
          malloc_token Tsh trelation p
  end.

Definition getCurrVal (c:cursor val): val :=
  match c with
  | [] => nullval
  | (n,_)::_ => match n with btnode _ _ _ x => x end
  end.

Definition getEntryIndex {X:Type} (c:cursor X) : nat :=
  match c with
  | (n,i)::_ => i
  | [] => 0%nat
  end.

Fixpoint cursor_valid_bool {X:Type} (c:cursor X): bool :=
  match c with
  | [] => true
  | (b,i)::c' => match b with btnode ptr0 le _ x => (i <=? (numKeys_le le))%nat && cursor_valid_bool c' end
  end.                          (* might be incomplete *)

Definition cursor_rep (c:cursor val) (r:relation val) (p:val):mpred :=
  EX anc_end:list val, EX idx_end:list val,
  malloc_token Tsh tcursor p *
  field_at Tsh tcursor (DOT _currNode) (getCurrVal c) p *
  match r with (n,c,x) => field_at Tsh tcursor (DOT _relation) x p end *
  field_at Tsh tcursor (DOT _entryIndex) (Vint(Int.repr(Z.of_nat(getEntryIndex c)))) p *
  field_at Tsh tcursor (DOT _isValid) (Val.of_bool (cursor_valid_bool c)) p *
  field_at Tsh tcursor (DOT _level) (Vint(Int.repr(Zlength c))) p *
  field_at Tsh tcursor (DOT _nextAncestorPointerIdx) ((map (fun x => Vint(Int.repr(Z.of_nat(snd x)))) c) ++ idx_end) p * (* or its reverse? *)
  field_at Tsh tcursor (DOT _ancestors) ((map getval (map fst c)) ++ anc_end) p.
(* what about the list length that can be shorter than the array? *)
(* also the index might be not exactly the same for intern nodes (no -1) *)

(**
    FUNCTION SPECIFICATIONS
 **)
Definition empty_node (b:bool) (p:val):node val := (btnode val) None (nil val) b p.
Definition empty_relation (pr:val) (pn:val): relation val := ((empty_node true pn),0%nat,pr).
Definition empty_cursor := []:cursor val.

Definition createNewNode_spec : ident * funspec :=
  DECLARE _createNewNode
  WITH isLeaf:bool
  PRE [ _isLeaf OF tint ]       (* why tint and not tbool? *)
  PROP ()
  LOCAL (temp _isLeaf (Val.of_bool isLeaf))
  SEP ()
  POST [ tptr tbtnode ]
  EX p:val, PROP ()
  LOCAL (temp ret_temp p)
  SEP (btnode_rep (empty_node isLeaf p) p).

Definition RL_NewRelation_spec : ident * funspec :=
  DECLARE _RL_NewRelation
  WITH u:unit
  PRE [ ]
  PROP ()
  LOCAL ()
  SEP ()
  POST [ tptr trelation ]
  EX pr:val, EX pn:val, PROP ()
  LOCAL(temp ret_temp pr)
  SEP (relation_rep (empty_relation pr pn) pr).

Definition RL_NewCursor_spec : ident * funspec :=
  DECLARE _RL_NewCursor
  WITH r:relation val, p:val
  PRE [ _relation OF tptr trelation ]
  PROP ()
  LOCAL (temp _relation p)
  SEP (relation_rep r p)
  POST [ tptr tcursor ]
  EX p':val, PROP ()
  LOCAL(temp ret_temp p')
  SEP (relation_rep r p * (if (eq_dec p' nullval)
                           then emp
                           else cursor_rep empty_cursor r p')).

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
  forward_call tbtnode.
  - admit.                      (* typecheck_error? *)
  - entailer!. admit.           (* false! *)
  - split. unfold sizeof. simpl. rep_omega.
    split. auto. admit.
  - Intros vret.
    forward_if (PROP (vret<>nullval)
     LOCAL (temp _newNode vret; temp _isLeaf (Val.of_bool isLeaf))
     SEP (if eq_dec vret nullval
          then emp
          else malloc_token Tsh tbtnode vret * data_at_ Tsh tbtnode vret; emp)).
    + admit.
    + forward. rewrite if_true; auto.
      admit.                    (* change the spec if malloc fails *)
    + forward. rewrite if_false; auto. entailer!.
    + Intros. rewrite if_false; auto. Intros.
      forward.                  (* newNode->numKeys = 0 *)
      forward.                  (* newnode->isLeaf=isLeaf *)
      forward.                  (* newnode->ptr0=null *)
      forward.                  (* return newnode *)
      Exists vret. entailer!.
      unfold_data_at 1%nat.
      entailer!.
Admitted.

Lemma body_NewRelation: semax_body Vprog Gprog f_RL_NewRelation RL_NewRelation_spec.
Proof.
start_function.
forward_call(true).
Intros vret.
forward_if (PROP (vret<>nullval)  LOCAL (temp _pRootNode vret)  SEP (btnode_rep (empty_node true vret) vret; emp)).
- subst vret.
  forward. entailer!.
- forward.
  entailer!.
- forward_call trelation.
  + admit.
  + entailer!.
    admit.                      (* false *)
  + split. unfold sizeof. simpl. rep_omega.
    split. auto. admit.
  + Intros newrel.
    forward_if(PROP (newrel<>nullval)
     LOCAL (temp _pNewRelation newrel; temp _pRootNode vret)
     SEP (if eq_dec newrel nullval
          then emp
          else malloc_token Tsh trelation newrel * data_at_ Tsh trelation newrel;
          btnode_rep (empty_node true vret) vret)).
    * apply denote_tc_test_eq_split.
      entailer!. admit.
      entailer!.
    * rewrite if_true; auto. subst newrel.
      forward_call (tbtnode, vret).
      { admit. }
      { forward. admit. }
    * rewrite if_false; auto.
      forward.
      entailer!. rewrite if_false; auto.
    * Intros. rewrite if_false; auto. Intros.
      forward.                  (* pnewrelation->root = prootnode *)
      forward.                  (* pnewrelation->numrecords=0 *)
      forward.                  (* return pnewrelation *)
      Exists newrel. Exists vret. Exists vret.
      entailer!.
      unfold_data_at 1%nat. cancel.
Admitted.

Lemma body_NewCursor: semax_body Vprog Gprog f_RL_NewCursor RL_NewCursor_spec.
Proof.
start_function.
forward_if (PROP() LOCAL(temp _relation p) SEP(relation_rep r p)).
- admit.
- forward. auto.
- subst p.
  (* forward_call tt. *)              (* telling me to import VST.floyd.library, but it has been done *)
  admit.
- forward_call tcursor.
  + admit.
  + entailer!. admit.
  + split. unfold sizeof. simpl. rep_omega.
    split. auto. admit.
  + Intros vret.
    forward_if ((PROP (vret<>nullval)
     LOCAL (temp _cursor vret; temp _relation p)
     SEP (if eq_dec vret nullval
          then emp
          else malloc_token Tsh tcursor vret * data_at_ Tsh tcursor vret; 
          relation_rep r p))).
    * admit.
    * rewrite if_true; auto.
      forward. Exists nullval. entailer!.
    * forward. rewrite if_false; auto. entailer!.
    * Intros. rewrite if_false; auto. Intros.
      forward.                  (* cursor->relation=relation *)
      forward.                  (* cursor->currnode=null *)
      forward.                  (* cursor->entryIndex=0 *)
      forward.                  (* cursor->isValid=0 *)
      forward.                  (* cursor->level=0 *)
      autorewrite with norm. simpl.

      Locate forward_for_simple_bound.
      Locate forward_for_simple_bound'.
      
      Ltac forward_for_simple_bound n Pre :=
        check_Delta; check_POSTCONDITION;
        repeat match goal with |-
                               semax _ _ (Ssequence (Ssequence (Ssequence _ _) _) _) _ =>
                               apply -> seq_assoc; abbreviate_semax
               end;
        first [
            match type of n with
              ?t => first [ unify t Z | elimtype (Type_of_bound_in_forward_for_should_be_Z_but_is t)]
            end;
            match type of Pre with
              ?t => first [unify t (environ -> mpred); fail 1 | elimtype (Type_of_invariant_in_forward_for_should_be_environ_arrow_mpred_but_is t)]
            end
          | simple eapply semax_seq';
            [forward_for_simple_bound' n Pre
            | cbv beta; simpl update_tycon; abbreviate_semax  ]
          | eapply semax_post_flipped';
            [forward_for_simple_bound' n Pre
            | ]
          ].

      Definition n:=20.
      pose (n:=20).
      pose (Pre:=(EX i:Z,
            PROP ()
            LOCAL(temp _cursor vret; temp _relation p)         
            SEP(malloc_token Tsh tcursor vret;
                relation_rep r p;
                data_at Tsh tcursor
               (force_val (sem_cast_pointer p),
               (Vint (Int.repr 0),
               (Vlong (Int64.repr 0),
               (Vint (Int.repr 0),
               (Vint (Int.repr 0),
               (list_repeat (Z.to_nat i) (Vint(Int.repr 0)) ++  list_repeat (MaxTreeDepth - (Z.to_nat i)) Vundef,
               (list_repeat (Z.to_nat i) nullval ++ list_repeat (MaxTreeDepth - (Z.to_nat i)) Vundef))))))) vret))%assert).

simple eapply semax_seq'.

(* forward_for_simple_bound n Pre. *)
Admitted.