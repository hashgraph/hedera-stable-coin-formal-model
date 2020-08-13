requires "hcs.k"

module COMPLIANT-SPEC
imports HCS

/*
  If and account is not frozen (default value) and has KYC set to false, and setKycPassed() is called, then checkTransferAllowed() should return true
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !Frozen[addr]
      * !KycPassed[addr]

  Post-conditions
      * KycPassed[addr]
      * result = true
 */
rule <k> setKycPassed(Target:Int, {caller: Caller})
         ~>
         checkTransferAllowed(Target:Int) => true ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <kycpassed> ... (Target |-> false => Target |-> true) ... </kycpassed>
     <frozen> ... (Target |-> false) ... </frozen>
  requires Owner =/=Int 0
    andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)

/*
  If and account is not frozen (default value) and has KYC set to false, and setKycPassed() is called and then freeze() is called,
  then checkTransferAllowed() should return false
  
  Pre-conditions
      * Owner != 0x
      * caller = AssetProtectionManager || caller = Owner
      * !Frozen[addr]
      * !KycPassed[addr]

  Post-conditions
      * KycPassed[addr]
      * Frozen[addr]
      * result = true
 */
rule <k> setKycPassed(Target:Int, {caller: Caller})
         ~>
         freeze(Target:Int, {caller: Caller})
         ~>
         checkTransferAllowed(Target:Int) => false ...</k>
     <tokenOwner> Owner </tokenOwner>
     <assetProtectionManager> AssetProtectionManager </assetProtectionManager>
     <supplyManager> SupplyManager </supplyManager>
     <kycpassed>... (Target |-> false => Target |-> true) ... </kycpassed>
     <frozen> ... (Target |-> false => Target |-> true) ... </frozen>
  requires Owner =/=Int 0
    andBool (Caller ==Int AssetProtectionManager orBool Caller ==Int Owner)
    andBool Target =/=Int Owner
    andBool Target =/=Int SupplyManager
    andBool Target =/=Int AssetProtectionManager

/*
  Detect transfer restriction
  
  Pre-conditions
      * Owner != 0x
      * Frozen[addr] || !KycPassed[addr]

  Post-conditions
      * result = false
 */
rule <k> checkTransferAllowed(Target:Int) => false ...</k>
     <tokenOwner> Owner </tokenOwner>
     <kycpassed>... (Target |-> ValK:Bool) ... </kycpassed>
     <frozen> ... (Target |-> ValF:Bool) ... </frozen>
  requires Owner =/=Int 0
    andBool (notBool ValK orBool ValF)

endmodule
