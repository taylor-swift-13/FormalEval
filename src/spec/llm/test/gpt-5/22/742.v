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

Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.

Parameter inj_Any_Z : Z -> Any.
Parameter inj_Any_list : list Any -> Any.
Parameter inj_Any_string : string -> Any.
Parameter inj_int_Z : Z -> int.

Axiom IsInt_inj_Z : forall z, IsInt (inj_Any_Z z) (inj_int_Z z).
Axiom IsInt_inj_list_false : forall l n, ~ IsInt (inj_Any_list l) n.

Example test_case_nested: filter_integers_spec
  [ inj_Any_Z 1%Z;
    inj_Any_list [inj_Any_Z 2%Z; inj_Any_string "3"%string];
    inj_Any_list [inj_Any_Z 5%Z; inj_Any_Z 6%Z];
    inj_Any_list [inj_Any_Z 7%Z; inj_Any_Z 8%Z];
    inj_Any_Z 9%Z;
    inj_Any_list [inj_Any_Z 7%Z; inj_Any_Z 8%Z] ]
  [ inj_int_Z 1%Z; inj_int_Z 9%Z ].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply IsInt_inj_Z.
  - eapply fir_cons_nonint.
    + intro n. exact (IsInt_inj_list_false [inj_Any_Z 2%Z; inj_Any_string "3"%string] n).
    + eapply fir_cons_nonint.
      * intro n. exact (IsInt_inj_list_false [inj_Any_Z 5%Z; inj_Any_Z 6%Z] n).
      * eapply fir_cons_nonint.
        { intro n. exact (IsInt_inj_list_false [inj_Any_Z 7%Z; inj_Any_Z 8%Z] n). }
        { eapply fir_cons_int.
          - apply IsInt_inj_Z.
          - eapply fir_cons_nonint.
            + intro n. exact (IsInt_inj_list_false [inj_Any_Z 7%Z; inj_Any_Z 8%Z] n).
            + apply fir_nil. }
Qed.