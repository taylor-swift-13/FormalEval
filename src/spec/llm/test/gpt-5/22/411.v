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

Parameters v_true v_false v_None v_real v_5 v_m7 v_1 v_a v_b v_nil1 v_nil2 v_unit v_list34 v_None2 v_list567 v_nil3 : Any.

Axiom IsInt_v5 : IsInt v_5 5%Z.
Axiom IsInt_vm7 : IsInt v_m7 (-7)%Z.
Axiom IsInt_v1 : IsInt v_1 1%Z.
Axiom NonInt_vtrue : forall n, ~ IsInt v_true n.
Axiom NonInt_vfalse : forall n, ~ IsInt v_false n.
Axiom NonInt_vNone : forall n, ~ IsInt v_None n.
Axiom NonInt_vreal : forall n, ~ IsInt v_real n.
Axiom NonInt_va : forall n, ~ IsInt v_a n.
Axiom NonInt_vb : forall n, ~ IsInt v_b n.
Axiom NonInt_vnil1 : forall n, ~ IsInt v_nil1 n.
Axiom NonInt_vnil2 : forall n, ~ IsInt v_nil2 n.
Axiom NonInt_vunit : forall n, ~ IsInt v_unit n.
Axiom NonInt_vlist34 : forall n, ~ IsInt v_list34 n.
Axiom NonInt_vNone2 : forall n, ~ IsInt v_None2 n.
Axiom NonInt_vlist567 : forall n, ~ IsInt v_list567 n.
Axiom NonInt_vnil3 : forall n, ~ IsInt v_nil3 n.

Example test_case_new:
  filter_integers_spec
    [v_true; v_false; v_None; v_real; v_5; v_m7; v_1; v_a; v_b; v_nil1; v_nil2; v_unit; v_list34; v_None2; v_list567; v_nil3]
    [5%Z; (-7)%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_nonint; [apply NonInt_vtrue |].
  eapply fir_cons_nonint; [apply NonInt_vfalse |].
  eapply fir_cons_nonint; [apply NonInt_vNone |].
  eapply fir_cons_nonint; [apply NonInt_vreal |].
  eapply fir_cons_int; [apply IsInt_v5 |].
  eapply fir_cons_int; [apply IsInt_vm7 |].
  eapply fir_cons_int; [apply IsInt_v1 |].
  eapply fir_cons_nonint; [apply NonInt_va |].
  eapply fir_cons_nonint; [apply NonInt_vb |].
  eapply fir_cons_nonint; [apply NonInt_vnil1 |].
  eapply fir_cons_nonint; [apply NonInt_vnil2 |].
  eapply fir_cons_nonint; [apply NonInt_vunit |].
  eapply fir_cons_nonint; [apply NonInt_vlist34 |].
  eapply fir_cons_nonint; [apply NonInt_vNone2 |].
  eapply fir_cons_nonint; [apply NonInt_vlist567 |].
  eapply fir_cons_nonint; [apply NonInt_vnil3 |].
  constructor.
Qed.