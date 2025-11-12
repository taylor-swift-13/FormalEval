
Require Import String.

Inductive RealType : Type :=
| IntVal : Z -> RealType
| FloatVal : float -> RealType
| StringVal : string -> RealType.

Definition compare_one_spec (a : RealType) (b : RealType) (result : option RealType) : Prop :=
  exists num_a num_b : float,
  (match a with
   | IntVal n => num_a = Z.to_float n
   | FloatVal f => num_a = f
   | StringVal s => exists s', s' = String.map (fun c => if (c = ",")%char then "."%char else c) s /\ num_a = float_of_string s'
   end) /\
  (match b with
   | IntVal n => num_b = Z.to_float n
   | FloatVal f => num_b = f
   | StringVal s => exists s', s' = String.map (fun c => if (c = ",")%char then "."%char else c) s /\ num_b = float_of_string s'
   end) /\
  (if (num_a =? num_b)%float then result = None
   else if (num_a >? num_b)%float then result = Some a
   else result = Some b).
