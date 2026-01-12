-- ATM Withdrawal: Monad Transformer Ordering
-- Run with: lake exe atm

-- ANCHOR: atm_types
/-- Errors that can occur during ATM withdrawal -/
inductive ATMError where
  | insufficientFunds (requested available : Nat)
  | dailyLimitExceeded (requested limit : Nat)
  | dispenserJam (dispensedBeforeJam : Nat)
  | cardRetained
  deriving Repr

def ATMError.describe : ATMError → String
  | .insufficientFunds req avail =>
      s!"Insufficient funds: requested ${req}, available ${avail}"
  | .dailyLimitExceeded req limit =>
      s!"Daily limit exceeded: requested ${req}, limit ${limit}"
  | .dispenserJam dispensed =>
      s!"Dispenser jam after dispensing ${dispensed}"
  | .cardRetained => "Card retained by machine"

/-- A single audit log entry with timestamp -/
structure AuditEntry where
  timestamp : Nat
  message : String
  deriving Repr

/-- The audit log tracks all operations for compliance -/
structure AuditLog where
  entries : List AuditEntry := []
  nextTimestamp : Nat := 0
  deriving Repr

def AuditLog.add (log : AuditLog) (msg : String) : AuditLog :=
  { entries := log.entries ++ [⟨log.nextTimestamp, msg⟩]
    nextTimestamp := log.nextTimestamp + 1 }

def AuditLog.show (log : AuditLog) : List String :=
  log.entries.map fun e => s!"[{e.timestamp}] {e.message}"

/-- Account information -/
structure Account where
  holder : String
  balance : Nat
  dailyWithdrawn : Nat := 0
  dailyLimit : Nat := 500
  deriving Repr
-- ANCHOR_END: atm_types

-- ANCHOR: atm_transformer_stacks
-- Two transformer orderings with DIFFERENT failure semantics:

-- Stack A: StateT outside Except
-- On error: audit log is LOST (transaction rollback)
-- Use case: atomic transactions where partial work should vanish
abbrev RollbackATM := StateT AuditLog (Except ATMError)

-- Stack B: ExceptT outside StateM
-- On error: audit log is PRESERVED (audit trail)
-- Use case: compliance logging where we must record what happened
abbrev AuditATM := ExceptT ATMError (StateM AuditLog)
-- ANCHOR_END: atm_transformer_stacks

-- ANCHOR: atm_positive_amount
/-- A positive amount - dependent type ensuring amount > 0 -/
def PosNat := { n : Nat // n > 0 }

def PosNat.mk? (n : Nat) : Option PosNat :=
  if h : n > 0 then some ⟨n, h⟩ else none

instance : Repr PosNat where
  reprPrec p _ := repr p.val
-- ANCHOR_END: atm_positive_amount

-- ANCHOR: atm_audit_operations
def logA (msg : String) : AuditATM Unit :=
  modify (·.add msg)

def checkBalanceA (acct : Account) (amount : PosNat) : AuditATM Unit := do
  logA s!"Balance check: ${acct.balance} available"
  if amount.val > acct.balance then
    logA s!"DENIED: Insufficient funds for ${amount.val}"
    throw (.insufficientFunds amount.val acct.balance)

def checkLimitA (acct : Account) (amount : PosNat) : AuditATM Unit := do
  let remaining := acct.dailyLimit - acct.dailyWithdrawn
  logA s!"Daily limit check: ${remaining} remaining of ${acct.dailyLimit}"
  if amount.val > remaining then
    logA s!"DENIED: Would exceed daily limit"
    throw (.dailyLimitExceeded amount.val acct.dailyLimit)

/-- The dispenser can jam AFTER partially dispensing cash -/
def dispenseCashA (amount : PosNat) : AuditATM Nat := do
  logA s!"Dispensing ${amount.val}..."
  -- Simulate dispenser jam on large withdrawals
  if amount.val > 200 then
    let dispensed := 100  -- $100 came out before jam
    logA s!"ERROR: Dispenser jam after ${dispensed} dispensed"
    throw (.dispenserJam dispensed)
  logA s!"Cash dispensed: ${amount.val}"
  pure amount.val

def updateBalanceA (acct : Account) (amount : Nat) : AuditATM Account := do
  let newBalance := acct.balance - amount
  logA s!"Balance updated: ${acct.balance} → ${newBalance}"
  pure { acct with balance := newBalance, dailyWithdrawn := acct.dailyWithdrawn + amount }
-- ANCHOR_END: atm_audit_operations

-- ANCHOR: atm_withdraw_audit
/-- Complete withdrawal with audit trail semantics -/
def withdrawAudit
    (acct : Account)
    (amount : PosNat) : AuditATM Account := do
  logA s!"=== Withdrawal started: {acct.holder} ==="
  logA s!"Requested amount: ${amount.val}"
  checkBalanceA acct amount
  checkLimitA acct amount
  let dispensed ← dispenseCashA amount
  let newAcct ← updateBalanceA acct dispensed
  logA s!"=== Withdrawal complete ==="
  pure newAcct
-- ANCHOR_END: atm_withdraw_audit

-- ANCHOR: atm_rollback_operations
def logR (msg : String) : RollbackATM Unit :=
  modify (·.add msg)

def checkBalanceR (acct : Account) (amount : PosNat) : RollbackATM Unit := do
  logR s!"Balance check: ${acct.balance} available"
  if amount.val > acct.balance then
    logR s!"DENIED: Insufficient funds for ${amount.val}"
    throw (.insufficientFunds amount.val acct.balance)

def checkLimitR (acct : Account) (amount : PosNat) : RollbackATM Unit := do
  let remaining := acct.dailyLimit - acct.dailyWithdrawn
  logR s!"Daily limit check: ${remaining} remaining of ${acct.dailyLimit}"
  if amount.val > remaining then
    logR s!"DENIED: Would exceed daily limit"
    throw (.dailyLimitExceeded amount.val acct.dailyLimit)

def dispenseCashR (amount : PosNat) : RollbackATM Nat := do
  logR s!"Dispensing ${amount.val}..."
  if amount.val > 200 then
    let dispensed := 100
    logR s!"ERROR: Dispenser jam after ${dispensed} dispensed"
    throw (.dispenserJam dispensed)
  logR s!"Cash dispensed: ${amount.val}"
  pure amount.val

def updateBalanceR (acct : Account) (amount : Nat) : RollbackATM Account := do
  let newBalance := acct.balance - amount
  logR s!"Balance updated: ${acct.balance} → ${newBalance}"
  pure { acct with balance := newBalance, dailyWithdrawn := acct.dailyWithdrawn + amount }

/-- Complete withdrawal with rollback semantics -/
def withdrawRollback
    (acct : Account)
    (amount : PosNat) : RollbackATM Account := do
  logR s!"=== Withdrawal started: {acct.holder} ==="
  logR s!"Requested amount: ${amount.val}"
  checkBalanceR acct amount
  checkLimitR acct amount
  let dispensed ← dispenseCashR amount
  let newAcct ← updateBalanceR acct dispensed
  logR s!"=== Withdrawal complete ==="
  pure newAcct
-- ANCHOR_END: atm_rollback_operations

-- ANCHOR: atm_running
/-- Run with audit semantics - log always preserved -/
def runAudit (acct : Account) (amount : PosNat)
    : (Except ATMError Account) × AuditLog :=
  let ((result, log)) :=
    StateT.run (ExceptT.run (withdrawAudit acct amount)) {}
  (result, log)

/-- Run with rollback semantics - log lost on error -/
def runRollback (acct : Account) (amount : PosNat)
    : Except ATMError (Account × AuditLog) :=
  StateT.run (withdrawRollback acct amount) {}
-- ANCHOR_END: atm_running

-- ANCHOR: atm_demo
def alice : Account := ⟨"Alice", 1000, 0, 500⟩

-- Small withdrawal: succeeds in both modes
#eval runAudit alice ⟨100, by omega⟩
-- (Except.ok {...}, AuditLog with entries)

-- Large withdrawal: dispenser jams!
#eval runAudit alice ⟨300, by omega⟩
-- (Except.error (dispenserJam 100), AuditLog PRESERVED)
-- The log shows exactly what happened before the error

#eval runRollback alice ⟨300, by omega⟩
-- Except.error (dispenserJam 100)
-- The log is LOST - we only know it failed
-- ANCHOR_END: atm_demo

-- ANCHOR: atm_compliance_horror
/--
The Compliance Horror:

With rollback semantics, when the dispenser jams after giving
Alice $100, the audit log is lost. The bank's records show nothing
happened. But Alice has $100 in her hand.

With audit semantics, the log is preserved:
  [0] === Withdrawal started: Alice ===
  [1] Requested amount: $300
  [2] Balance check: $1000 available
  [3] Daily limit check: $500 remaining of $500
  [4] Dispensing $300...
  [5] ERROR: Dispenser jam after 100 dispensed

Now compliance knows: Alice got $100, the machine jammed,
and manual reconciliation is needed.

This is why banks use audit semantics for ATM transactions.
Financial regulations require knowing what happened, not just
whether it succeeded.
-/
def demonstrateDifference : IO Unit := do
  IO.println "=== Rollback Semantics (StateT outside Except) ==="
  IO.println "On error, the audit log is LOST\n"

  let amount : PosNat := ⟨300, by omega⟩
  match runRollback alice amount with
  | .ok (acct, log) =>
    IO.println s!"Success! New balance: ${acct.balance}"
    IO.println "Audit log:"
    for entry in log.show do IO.println s!"  {entry}"
  | .error e =>
    IO.println s!"FAILED: {e.describe}"
    IO.println "Audit log: <LOST - we only have the error>"
    IO.println "Compliance cannot determine what happened.\n"

  IO.println "\n=== Audit Semantics (ExceptT outside StateM) ==="
  IO.println "On error, the audit log is PRESERVED\n"

  let (result, log) := runAudit alice amount
  match result with
  | .ok acct =>
    IO.println s!"Success! New balance: ${acct.balance}"
  | .error e =>
    IO.println s!"FAILED: {e.describe}"
  IO.println "Audit log (preserved!):"
  for entry in log.show do IO.println s!"  {entry}"
  IO.println "\nCompliance can see exactly what happened."
-- ANCHOR_END: atm_compliance_horror

def main : IO Unit := do
  IO.println "=== ATM Withdrawal: Transformer Ordering Demo ===\n"

  IO.println "--- Successful Withdrawal ($100) ---"
  let (result, log) := runAudit alice ⟨100, by omega⟩
  match result with
  | .ok acct => IO.println s!"New balance: ${acct.balance}"
  | .error e => IO.println s!"Error: {e.describe}"
  for entry in log.show do IO.println s!"  {entry}"

  IO.println "\n--- Failed Withdrawal ($300 - dispenser jam) ---"
  demonstrateDifference

  IO.println "\n--- The Key Insight ---"
  IO.println "Transformer ordering determines failure semantics:"
  IO.println "  StateT S (Except E) → state lost on error (rollback)"
  IO.println "  ExceptT E (StateM S) → state kept on error (audit)"
  IO.println "\nChoose based on your requirements:"
  IO.println "  - Database transactions: rollback semantics"
  IO.println "  - Financial compliance: audit semantics"
