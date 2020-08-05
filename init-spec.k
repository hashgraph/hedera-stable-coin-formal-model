requires "hcs.k"

module INIT-SPEC
  imports HCS

  rule <k> initAccount(Account) => . ...</k>
      <balances> ... (.Map => Account |-> 0) ... </balances>
      <frozen> ... (.Map => Account |-> false) ... </frozen>
      <kycpassed> ... (.Map => Account |-> false) ... </kycpassed>
      <tokenOwner> Owner </tokenOwner>
       <allowances>
       Allowances => 
         Allowances
         <allowance>
           <allower> Account </allower>
           <spenders> (0 |-> 0) </spenders>
         </allowance>
      </allowances>
    requires Owner =/=Int 0
endmodule