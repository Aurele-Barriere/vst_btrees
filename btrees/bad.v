(** * verif_btrees.v: Correctness proof of relation_mem.c *)

Require Import VST.floyd.proofauto.
Require Import VST.floyd.library.
Require Import relation_mem.
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Require Import VST.msl.wand_frame.
Require Import VST.msl.iter_sepcon.
Require Import VST.floyd.reassoc_seq.
Require Import VST.floyd.field_at_wand.

Definition key := Z.            (* unsigned long in C *)

Section BTrees.
Variable V : Type.
Variable b : nat.

Inductive node: Type :=
| L: leafnode -> node
| I: internnode -> node
with leafnode: Type :=
| LN: leafnode
| LE: valentrylist -> leafnode
with internnode: Type :=
| IN: internnode
| IE: node -> childentrylist -> internnode (* first node is ptr0 *)
with valentrylist: Type :=      (* nonempty *)
| VELO: key -> V -> valentrylist
| VELC: key -> V -> valentrylist -> valentrylist
with childentrylist: Type :=    (* nonempty *)
| CELO: key -> node -> childentrylist
| CELC: key -> node -> childentrylist -> childentrylist.

Definition cursor: Type := list Z. (* ancestors index *)

Definition empty_tree: node := L LN.

Fixpoint vel_length (vl: valentrylist) :=
  match vl with
  | VELO _ _ => 1
  | VELC _ _ vl' => 1+ vel_length vl'
  end.

Fixpoint cel_length (cl: childentrylist) :=
  match cl with
  | CELO _ _ => 1
  | CELC _ _ cl' => 1+ cel_length cl'
  end.

Definition node_length (n:node):=
  match n with
  | L l => match l with
           | LN => 0
           | LE vl => vel_length vl
           end
  | I i => match i with
           | IN => 0
           | IE ptr0 cl => cel_length cl
           end
  end.

Lemma empty_empty_tree: node_length empty_tree = 0.
Proof. auto. Qed.

Definition cursor_valid: cursor -> node -> Prop.
  Admitted.