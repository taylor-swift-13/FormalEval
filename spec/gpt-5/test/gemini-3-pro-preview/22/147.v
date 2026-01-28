Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Import ListNotations.

Parameter Any : Type.
Definition int := Z.
Parameter IsInt : Any -> int -> Prop.
Axiom IsInt_functional : forall v n m, IsInt v n -> IsInt v m -> n = m.

Parameter inj_int : Z -> Any.
Parameter inj_str : string -> Any.
Parameter inj_list : list Any -> Any.
Parameter inj_dict : Any.

Axiom IsInt_inj_int : forall z, IsInt (inj_int z) z.
Axiom NotIsInt_inj_str : forall s n, ~ IsInt (inj_str s) n.
Axiom NotIsInt_inj_list : forall l n, ~ IsInt (inj_list l) n.
Axiom NotIsInt_inj_dict : forall n, ~ IsInt inj_dict n.

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

Example test_filter_integers_mixed :
  filter_integers_spec
    [inj_int 2; inj_int 1; inj_str "one"; inj_list [inj_int 1; inj_int 2; inj_int 3]; inj_dict]
    [2%Z; 1%Z].
Proof.
  unfold filter_integers_spec.
  apply fir_cons_int with (n := 2%Z).
  - apply IsInt_inj_int.
  - apply fir_cons_int with (n := 1%Z).
    + apply IsInt_inj_int.
    + apply fir_cons_nonint.
      * apply NotIsInt_inj_str.
      * apply fir_cons_nonint.
        -- apply NotIsInt_inj_list.
        -- apply fir_cons_nonint.
           ++ apply NotIsInt_inj_dict.
           ++ apply fir_nil.
Qed.