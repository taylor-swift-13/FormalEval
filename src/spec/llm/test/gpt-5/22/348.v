Require Import Coq.Lists.List.
Import ListNotations.

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

Example test_case_mixed :
  forall (v98 v1 v2 v4 vfour v55 v6 v33 v8 : Any)
         (n98 n1 n2 n4 n6 : int),
    IsInt v98 n98 ->
    IsInt v1 n1 ->
    IsInt v2 n2 ->
    IsInt v4 n4 ->
    (forall n, ~ IsInt vfour n) ->
    (forall n, ~ IsInt v55 n) ->
    IsInt v6 n6 ->
    (forall n, ~ IsInt v33 n) ->
    (forall n, ~ IsInt v8 n) ->
    filter_integers_spec [v98; v1; v2; v4; vfour; v55; v6; v33; v8]
                         [n98; n1; n2; n4; n6].
Proof.
  intros v98 v1 v2 v4 vfour v55 v6 v33 v8 n98 n1 n2 n4 n6
         H98 H1 H2 H4 Hfour H55 H6 H33 H8.
  unfold filter_integers_spec.
  eapply fir_cons_int; [exact H98|].
  eapply fir_cons_int; [exact H1|].
  eapply fir_cons_int; [exact H2|].
  eapply fir_cons_int; [exact H4|].
  eapply fir_cons_nonint; [exact Hfour|].
  eapply fir_cons_nonint; [exact H55|].
  eapply fir_cons_int; [exact H6|].
  eapply fir_cons_nonint; [exact H33|].
  eapply fir_cons_nonint; [exact H8|].
  constructor.
Qed.