requires "erc20.k"

module COMPLIANT-SPEC
imports ERC20

// compliant - setKycPassed and checkTransferAllowed, which is a happy path
rule <k> setKycPassed(Target:Int, {caller: Caller})
         ~>
         checkTransferAllowed(Target:Int) => true ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <kycpassed> ... (Target |-> false => Target |-> true) ... </kycpassed>
     <frozen> ... (Target |-> false) ... </frozen>
  requires Owner =/=Int 0
    andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

// compliant - setKycPassed, freeze, then checkTransferAllowed, which is a bad path
rule <k> setKycPassed(Target:Int, {caller: Caller})
         ~>
         freeze(Target:Int, {caller: Caller})
         ~>
         checkTransferAllowed(Target:Int) => false ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <kycpassed>... (Target |-> false => Target |-> true) ... </kycpassed>
     <frozen> ... (Target |-> false => Target |-> true) ... </frozen>
  requires Owner =/=Int 0
    andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

// compliant - `checkTransferAllowed` without first calling `setKycPassed`, which is a bad path
rule <k> checkTransferAllowed(Target:Int) => false ...</k>
     <tokenOwner> Owner </tokenOwner>
     <kycpassed>... (Target |-> ValK:Bool) ... </kycpassed>
     <frozen> ... (Target |-> ValF:Bool) ... </frozen>
  requires Owner =/=Int 0
    andBool (notBool ValK orBool ValF)

endmodule
