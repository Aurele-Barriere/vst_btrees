Require Import VST.floyd.proofauto. (* Import the Verifiable C system *)
Require Import sum. (* Import the AST of this C program *)
(* The next line is "boilerplate", always required after importing an AST. *)
Instance CompSpecs : compspecs. make_compspecs prog. Defined.
Definition Vprog : varspecs.  mk_varspecs prog. Defined.

Definition sum_Z : Z -> Z -> Z := Z.add.

Lemma sum_com :
  forall a b, sum_Z a b = sum_Z b a.
Proof.
  intros. unfold sum_Z. omega.
Qed.

Definition sum_spec : ident * funspec :=
 DECLARE _sum
  WITH a: Z, b: Z
  PRE [ _a OF tint, _b OF tint ]
          PROP  (Int.min_signed <= a <= Int.max_signed; Int.min_signed <= b <= Int.max_signed)
          LOCAL (temp _a (Vint (Int.repr a)); temp _b (Vint (Int.repr b)))
          SEP   ()
  POST [ tint ]
        PROP () LOCAL(temp ret_temp  (Vint (Int.repr (sum_Z a b))))
           SEP ().

Definition main_spec :=
 DECLARE _main
  WITH u : unit
  PRE  [] main_pre prog nil u
  POST [ tint ]  
     PROP() 
     LOCAL (temp ret_temp (Vint (Int.repr (2+3)))) 
     SEP(TT).

Definition Gprog : funspecs :=
        ltac:(with_library prog [sum_spec; main_spec]).

Lemma body_sum: semax_body Vprog Gprog f_sum sum_spec.
Proof.
  start_function.
  forward.
  entailer!.
Admitted.  