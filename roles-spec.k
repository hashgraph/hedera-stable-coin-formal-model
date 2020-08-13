requires "hcs.k"

module ROLES-SPEC
  imports HCS

/*
  Owner can propose a new owner.
  
  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * ProposedOwner = addr
*/
rule <k> proposeOwner(ProposedOwner, { caller : Caller } ) => . ...</k>
     <tokenOwner> Caller </tokenOwner>
     <proposedOwner> _ => ProposedOwner </proposedOwner>
     <kycpassed> ... (ProposedOwner |-> true) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ProposedOwner =/=Int 0

/*
  Proposing owner twice ignores the first call.
  
  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * ProposedOwner1 != 0x
      * ProposedOwner2 != 0x
      * CheckTransferAllowed(ProposedOwner1)
      * CheckTransferAllowed(ProposedOwner2)

  Post-conditions
      * ProposedOwner = ProposedOwner2
*/
rule <k> proposeOwner(ProposedOwner1, { caller : Caller } )
         ~>
         proposeOwner(ProposedOwner2, { caller : Caller } ) => . ...</k>
     <tokenOwner> Caller </tokenOwner>
     <proposedOwner> _ => ProposedOwner2 </proposedOwner>
     <kycpassed> ... (ProposedOwner1 |-> true)(ProposedOwner2 |-> true) ... </kycpassed>
     <frozen> ... (ProposedOwner1 |-> false)(ProposedOwner2 |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ProposedOwner1 =/=Int 0 andBool ProposedOwner2 =/=Int 0

// non-owner cannot propose a new owner
rule <k> proposeOwner(ProposedOwner:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <kycpassed> ... (ProposedOwner |-> _) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> _) ... </frozen>
  requires TokenOwner =/=Int Caller
 
/*
  Proposed owner can claim ownership and the proposed owner is then reset.
  
  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * ProposedOwner = 0
      * Owner = addr
*/
rule <k> proposeOwner(ProposedOwner, { caller : Caller } )
         ~>
         claimOwnership( { caller : ProposedOwner } ) => . ...</k>
     <tokenOwner> Caller => ProposedOwner </tokenOwner>
     <proposedOwner> _ => 0 </proposedOwner>
     <kycpassed> ... (ProposedOwner |-> true) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool ProposedOwner =/=Int 0

// nobody besides the proposed owner can claim ownership
rule <k> proposeOwner(ProposedOwner:Int, { caller : Caller:Int } )
         ~>
         claimOwnership( { caller : AnotherCaller:Int } ) => throw ...</k>
     <tokenOwner> Caller </tokenOwner>
     <proposedOwner> _ => ProposedOwner </proposedOwner>
     <kycpassed> ... (ProposedOwner |-> true)(AnotherCaller |-> _) ... </kycpassed>
     <frozen> ... (ProposedOwner |-> false)(AnotherCaller |-> _) ... </frozen>
  requires Caller =/=Int 0
    andBool AnotherCaller =/=Int 0
    andBool ProposedOwner =/=Int 0
    andBool ProposedOwner =/=Int AnotherCaller

/*
  Owner can change supply manager
  
  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * SupplyManager = addr
*/
rule <k> changeSupplyManager(SupplyManager, { caller : Caller } ) => . ...</k>
     <tokenOwner> Caller </tokenOwner>
     <supplyManager> _ => SupplyManager </supplyManager>
     <kycpassed> ... (SupplyManager |-> true) ... </kycpassed>
     <frozen> ... (SupplyManager |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool SupplyManager =/=Int 0

// non-owner cannot change supply manager
rule <k> changeSupplyManager(SupplyManager:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <kycpassed> ... (SupplyManager |-> _) ... </kycpassed>
     <frozen> ... (SupplyManager |-> _) ... </frozen>
  requires TokenOwner =/=Int Caller

/*
  Owner can change asset protection manager.

  Pre-conditions
      * Owner != 0x
      * caller = Owner
      * addr != 0x
      * CheckTransferAllowed(addr)

  Post-conditions
      * AssetProtectionManager = addr
 */
rule <k> changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } ) =>  . ...</k>
     <tokenOwner> Caller </tokenOwner>
     <assetProtectionManager> _ => AssetProtectionManager </assetProtectionManager>
     <kycpassed> ... (AssetProtectionManager |-> true) ... </kycpassed>
     <frozen> ... (AssetProtectionManager |-> false) ... </frozen>
  requires Caller =/=Int 0 andBool AssetProtectionManager =/=Int 0

// non-owner cannot change asset protection manager
rule <k> changeAssetProtectionManager(AssetProtectionManager:Int, { caller : Caller } ) => throw ...</k>
     <tokenOwner> TokenOwner </tokenOwner>
     <kycpassed> ... (AssetProtectionManager |-> _) ... </kycpassed>
     <frozen> ... (AssetProtectionManager |-> _) ... </frozen>
  requires TokenOwner =/=Int Caller

endmodule