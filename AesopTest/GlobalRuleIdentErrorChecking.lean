/-
Copyright (c) 2024 Jannis Limperg. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jannis Limperg
-/

import Aesop
namespace GlobalRuleIdentErrorChecking
set_option aesop.collectStats true

/--
error: duplicate rule 'Nat.add_assoc'; rule 'GlobalRuleIdentErrorChecking.bar' was already given.
Use [<term>,...] to give multiple rules.
-/
#guard_msgs in
@[aesop norm simp Nat.add_assoc]
theorem bar : True := trivial
