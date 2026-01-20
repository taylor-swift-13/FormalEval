Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Reals.Reals.

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

Parameter injZ_to_Any : Z -> Any.
Parameter injString_to_Any : string -> Any.
Parameter injR_to_Any : R -> Any.
Parameter injZ_to_int : Z -> int.

Axiom IsInt_of_Z : forall z, IsInt (injZ_to_Any z) (injZ_to_int z).
Axiom NotInt_b : forall n, ~ IsInt (injString_to_Any "b") n.
Axiom NotInt_9_0 : forall n, ~ IsInt (injR_to_Any 9.0%R) n.

Example test_case_mixed:
  filter_integers_spec
    [injZ_to_Any 1%Z; injZ_to_Any 2%Z; injZ_to_Any 10%Z; injZ_to_Any 4%Z; injString_to_Any "b"; injR_to_Any 9.0%R]
    [injZ_to_int 1%Z; injZ_to_int 2%Z; injZ_to_int 10%Z; injZ_to_int 4%Z].
Proof.
  unfold filter_integers_spec.
  eapply fir_cons_int.
  - apply IsInt_of_Z.
  - eapply fir_cons_int.
    + apply IsInt_of_Z.
    + eapply fir_cons_int.
      * apply IsInt_of_Z.
      * eapply fir_cons_int.
        { apply IsInt_of_Z. }
        { eapply fir_cons_nonint.
          - apply NotInt_b.
          - eapply fir_cons_nonint.
            + apply NotInt_9_0.
            + apply fir_nil. }
Qed.