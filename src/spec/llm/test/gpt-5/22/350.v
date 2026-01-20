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

Parameter v1 v23 v4 v56 vnil v7_8 vdict v9 v56' vnil' : Any.
Axiom IsInt_v1_1 : IsInt v1 1%Z.
Axiom NotInt_v23 : forall n, ~ IsInt v23 n.
Axiom IsInt_v4_4 : IsInt v4 4%Z.
Axiom NotInt_v56 : forall n, ~ IsInt v56 n.
Axiom NotInt_vnil : forall n, ~ IsInt vnil n.
Axiom NotInt_v7_8 : forall n, ~ IsInt v7_8 n.
Axiom NotInt_vdict : forall n, ~ IsInt vdict n.
Axiom NotInt_v9 : forall n, ~ IsInt v9 n.
Axiom NotInt_v56' : forall n, ~ IsInt v56' n.
Axiom NotInt_vnil' : forall n, ~ IsInt vnil' n.

Example test_case_mixed: filter_integers_spec [v1; v23; v4; v56; vnil; v7_8; vdict; v9; v56'; vnil'] [1%Z; 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int; [apply IsInt_v1_1 |].
  eapply fir_cons_nonint; [apply NotInt_v23 |].
  eapply fir_cons_int; [apply IsInt_v4_4 |].
  eapply fir_cons_nonint; [apply NotInt_v56 |].
  eapply fir_cons_nonint; [apply NotInt_vnil |].
  eapply fir_cons_nonint; [apply NotInt_v7_8 |].
  eapply fir_cons_nonint; [apply NotInt_vdict |].
  eapply fir_cons_nonint; [apply NotInt_v9 |].
  eapply fir_cons_nonint; [apply NotInt_v56' |].
  eapply fir_cons_nonint; [apply NotInt_vnil' |].
  apply fir_nil.
Qed.