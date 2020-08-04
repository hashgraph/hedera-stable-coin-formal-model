requires "erc20.k"

module TRANSFERABLE-SPEC
imports ERC20

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