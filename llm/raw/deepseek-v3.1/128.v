
Require Import List ZArith.
Import ListNotations.

Definition prod_signs_spec (arr : list Z) (result : option Z) : Prop :=
  match arr with
  | [] => result = None
  | _ => if existsb (fun x => x =? 0) arr then result = Some 0
         else exists s sgn, 
              fold_left (fun acc x => acc + Z.abs x) arr 0 = s /\
              fold_left (fun acc x => acc * (x / Z.abs x)) arr 1 = sgn /\
              result = Some (s * sgn)
  end.
