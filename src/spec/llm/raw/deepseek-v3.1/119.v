
Require Import String List Bool ZArith.
Open Scope string_scope.

Definition valid_parens (s : string) : bool :=
  let fix go (s : string) (cnt : Z) : bool :=
    match s with
    | "" => Z.eqb cnt 0
    | String "(" s' => if Z.ltb cnt 0 then false else go s' (cnt + 1)
    | String ")" s' => if Z.ltb (cnt - 1) 0 then false else go s' (cnt - 1)
    | _ => false
    end
  in go s 0.

Definition match_parens_spec (lst : list string) (result : string) : Prop :=
  match lst with
  | [s1; s2] => 
      (result = "Yes" <-> (valid_parens (s1 ++ s2) = true \/ valid_parens (s2 ++ s1) = true)) /\
      (result = "No" <-> (valid_parens (s1 ++ s2) = false /\ valid_parens (s2 ++ s1) = false))
  | _ => False
  end.
