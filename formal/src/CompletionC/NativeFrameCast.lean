import PricingC.ThreeSupportFrame
set_option autoImplicit false
namespace CompletionC.NativeFrameCast
open Ramsey61 Ramsey61.CEncodingCore PricingC.ThreeSupportFrame
noncomputable def castFrame {c:Host} {a b d x y z:Nat}
 (f:Frame c a b d) (h0:a=x) (h1:b=y) (h2:d=z):Frame c x y z:=by
 subst x;subst y;subst z;exact f

theorem free_value {c:Host} {a b d x y z:Nat}
 (f:Frame c a b d) (h0:a=x) (h1:b=y) (h2:d=z)
 (i:Fin x) (j:Fin a) (h:i.val=j.val):
 (castFrame f h0 h1 h2).free i=f.free j:=by
 subst x;subst y;subst z;exact congrArg f.free (Fin.ext h)
theorem left_value {c:Host} {a b d x y z:Nat}
 (f:Frame c a b d) (h0:a=x) (h1:b=y) (h2:d=z)
 (i:Fin y) (j:Fin b) (h:i.val=j.val):
 (castFrame f h0 h1 h2).left i=f.left j:=by
 subst x;subst y;subst z;exact congrArg f.left (Fin.ext h)
theorem right_value {c:Host} {a b d x y z:Nat}
 (f:Frame c a b d) (h0:a=x) (h1:b=y) (h2:d=z)
 (i:Fin z) (j:Fin d) (h:i.val=j.val):
 (castFrame f h0 h1 h2).right i=f.right j:=by
 subst x;subst y;subst z;exact congrArg f.right (Fin.ext h)
end CompletionC.NativeFrameCast
