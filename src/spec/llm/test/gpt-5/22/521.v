Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.

Parameter Any : Type.
Parameter int : Type.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Inductive filter_integers_rel : list Any -> list int -> Prop :=
| fir_nil : filter_integers_rel [] []
| fir_cons_int v n vs res :
    IsInt v n ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) (n :: res)
| fir_cons_nonint v vs res :
    (forall n, ~ IsInt v n) ->
    filter_integers_rel vs res ->
    filter_integers_rel (v :: vs) res.

Definition filter_integers_spec (values : list Any) (res : list int) : Prop :=
  filter_integers_rel values res.

Parameter inj_any : Z -> Any.
Parameter inj_int : Z -> int.
Axiom IsInt_inj : forall z, IsInt (inj_any z) (inj_int z).

Parameter list_7_8_8 : Any.
Axiom list_7_8_8_nonint : forall n, ~ IsInt list_7_8_8 n.
Parameter empty_list : Any.
Axiom empty_list_nonint : forall n, ~ IsInt empty_list n.

Example test_case_new: filter_integers_spec [inj_any (-85%Z); list_7_8_8; inj_any 1%Z; empty_list; empty_list; list_7_8_8; inj_any 7%Z; empty_list] [inj_int (-85%Z); inj_int 1%Z; inj_int 7%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_inj|].
  eapply fir_cons_nonint; [apply list_7_8_8_nonint|].
  eapply fir_cons_int; [apply IsInt_inj|].
  eapply fir_cons_nonint; [apply empty_list_nonint|].
  eapply fir_cons_nonint; [apply empty_list_nonint|].
  eapply fir_cons_nonint; [apply list_7_8_8_nonint|].
  eapply fir_cons_int; [apply IsInt_inj|].
  eapply fir_cons_nonint; [apply empty_list_nonint|].
  constructor.
Qed.