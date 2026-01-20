Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
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

Parameter v0 v2 v3 v_foneour v_5_5 v6 v_seven v8 v_9_0 : Any.

Axiom IsInt_v0 : IsInt v0 0%Z.
Axiom IsInt_v2 : IsInt v2 2%Z.
Axiom IsInt_v3 : IsInt v3 3%Z.
Axiom IsInt_v6 : IsInt v6 6%Z.

Axiom NonInt_v_foneour : forall n, ~ IsInt v_foneour n.
Axiom NonInt_v_5_5 : forall n, ~ IsInt v_5_5 n.
Axiom NonInt_v_seven : forall n, ~ IsInt v_seven n.
Axiom NonInt_v8 : forall n, ~ IsInt v8 n.
Axiom NonInt_v_9_0 : forall n, ~ IsInt v_9_0 n.

Example test_case_mixed:
  filter_integers_spec
    [v0; v2; v3; v_foneour; v_5_5; v6; v_seven; v8; v_9_0]
    [0%Z; 2%Z; 3%Z; 6%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v0|].
  eapply fir_cons_int; [apply IsInt_v2|].
  eapply fir_cons_int; [apply IsInt_v3|].
  eapply fir_cons_nonint; [apply NonInt_v_foneour|].
  eapply fir_cons_nonint; [apply NonInt_v_5_5|].
  eapply fir_cons_int; [apply IsInt_v6|].
  eapply fir_cons_nonint; [apply NonInt_v_seven|].
  eapply fir_cons_nonint; [apply NonInt_v8|].
  eapply fir_cons_nonint; [apply NonInt_v_9_0|].
  constructor.
Qed.