requires "hcs.k"

module TRANSFERABLE-SPEC
imports HCS

/*
  Transfer
  
  Pre-conditions
      * Owner != 0x
      * value >= 0
      * Balances[From] >= value
      * CheckTransferAllowed(From)
      * CheckTransferAllowed(To)
      * To != From

  Post-conditions
      * Balances[From]’ = Balances[From] - value
      * Balances[To]' = Balances[To] + value
 */
rule <k> transfer(To, Value, { caller : From } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <balances> ... (From |-> BalanceFrom => From |-> BalanceFrom -Int Value)
                    (To |-> BalanceTo => To |-> BalanceTo +Int Value) ... </balances>
     <kycpassed> ... (To |-> true) (From |-> true) ... </kycpassed>
     <frozen> ... (To |-> false) (From |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool To =/=Int From
    andBool Value >=Int 0
    andBool BalanceFrom >=Int Value

/*
  Transfer followed by another transfer should update the three involved accounts correctly.
  
  Pre-conditions
      * Owner != 0x
      * value1 >= 0
      * value2 >= 0
      * Balances[Acc1] >= value1
      * Balances[Acc2] + value1 >= value2
      * CheckTransferAllowed(Acc1)
      * CheckTransferAllowed(Acc2)
      * CheckTransferAllowed(Acc3)
      * Acc2 != Acc1
      * Acc3 != Acc2

  Post-conditions
      * Balances[Acc1]’ = Balances[Acc1] - value1
      * Balances[Acc2]' = Balances[Acc2] + value1 - value2
      * Balances[Acc3]' = Balances[Acc3] + value2
 */
rule <k> transfer(Acc2, Value1, { caller : Acc1 } )
         ~>
         transfer(Acc3, Value2, { caller : Acc2 } ) => . ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <balances> ... (Acc1 |-> BalanceAcc1 => Acc1 |-> BalanceAcc1 -Int Value1)
                    (Acc2 |-> BalanceAcc2 => Acc2 |-> BalanceAcc2 +Int Value1 -Int Value2)
                    (Acc3 |-> BalanceAcc3 => Acc3 |-> BalanceAcc3 +Int Value2) ... </balances>
     <kycpassed> ... (Acc3 |-> true) (Acc2 |-> true) (Acc1 |-> true) ... </kycpassed>
     <frozen> ... (Acc3 |-> false) (Acc2 |-> false) (Acc1 |-> false) ... </frozen>
  requires TokenOwner =/=Int 0
    andBool Acc2 =/=Int Acc1
    andBool Acc3 =/=Int Acc2
    andBool Value1 >=Int 0
    andBool Value2 >=Int 0
    andBool BalanceAcc1 >=Int Value1
    andBool BalanceAcc2 +Int Value1 >=Int Value2

/*
  Transfer tokens on behalf of the owner

  Pre-conditions
      * Owner != 0x
      * value >= 0
      * Balances[from] >= value
      * Allowances[from][caller] >= value
      * CheckTransferAllowed(caller)
      * CheckTransferAllowed(from)
      * CheckTransferAllowed(to)

  Post-conditions
      * Balances[from]’ = Balances[from] - value
      * Allowances[from][caller]’ = Allowances[from][caller] - value
      * Balances[to]’ = Balances[to] + value
 */
rule <k> transferFrom(From:Int, To:Int, Value:Int, {caller: Caller:Int}) => . ... </k>
       <tokenOwner> TokenOwner </tokenOwner>
       <allowance>
         <allower> From </allower>
         <spenders> ... (Caller |-> Allowance => Caller |-> Allowance -Int Value) ... </spenders>
       </allowance>
       <balances> ... (From |-> BalanceFrom => From |-> BalanceFrom -Int Value)
                      (To |-> BalanceTo => To |-> BalanceTo +Int Value) ... </balances>
       <kycpassed> ... (To |-> true) (From |-> true) (Caller |-> true) ... </kycpassed>
       <frozen> ... (To |-> false) (From |-> false) (Caller |-> false) ... </frozen>
    requires TokenOwner =/=Int 0
      andBool To =/=Int From
      andBool Value >=Int 0
      andBool BalanceFrom >=Int Value
      andBool Allowance >=Int Value

endmodule