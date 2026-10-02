/-
Copyright (c) 2026 PolyFun Contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Devon Tuma
-/

module

public import Parliament.Interaction
public import PolyFunIO.Console

/-! # From a typed attendance form to a certified polynomial input

This is the small entry point before the full meeting application. Parsing does not confer
authority. The domain checker checks the chair, roster, and invariants, then returns an indexed
direction that the dynamical system can consume. A memory console runs exactly the same form.
-/

@[expose] public section

namespace Parliament.Walkthrough

open PolyFunIO

-- BEGIN ATTENDANCE
/-- Construct a command without performing IO or claiming it is authorized. -/
def attendanceForm {D : MotionDomain} : Form (Command D) := do
  return .attendance (← Form.natural "Chair ID: ") (← Form.natural "Member ID: ")
    (← Form.boolean "Present (yes/no): ")

/-- Input errors and domain rejections remain different outcomes. -/
def checkedAttendance (rules : Rules) (state : AssemblyState wordDomain) :
    Form (Except RuleError (EnabledInput rules state)) := do
  return checkInput rules state (← attendanceForm)
-- END ATTENDANCE

/-- Certified input updates use the library's state-dependent polynomial source map. -/
theorem attendance_update (rules : Rules) (state : AssemblyState wordDomain)
    (input : EnabledInput rules state) :
    (meetingSystem wordDomain rules).update state input = input.next := rfl

end Parliament.Walkthrough
