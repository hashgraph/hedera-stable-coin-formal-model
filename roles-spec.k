requires "erc20.k"

module ROLES-SPEC
  imports ERC20

// owner can propose a new owner
rule
    <k>
        proposeOwner(ProposedOwner, { caller : Caller } )
      => 
        .
    ...</k>
    <tokenOwner> Caller </tokenOwner>
    <proposedOwner> _ => ProposedOwner </proposedOwner>
requires Caller =/=Int 0
    andBool ProposedOwner =/=Int 0

// non-owner cannot propose a new owner
rule
    <k>
        proposeOwner(_:Int, { caller : Caller } )
      =>
        throw
    ...</k>
    <tokenOwner> TokenOwner </tokenOwner>
requires TokenOwner =/=Int Caller

// proposed owner can claim ownership
rule
    <k>
        proposeOwner(ProposedOwner, { caller : Caller } )
        ~>
        claimOwnership( { caller : ProposedOwner } )
      =>
         .
    ...</k>
    <tokenOwner> Caller => ProposedOwner </tokenOwner>
    <proposedOwner> _ => 0 </proposedOwner>
requires Caller =/=Int 0
    andBool ProposedOwner =/=Int 0

// nobody besides the proposed owner can claim ownership
rule
    <k>
        proposeOwner(ProposedOwner, { caller : Caller } )
        ~>
        claimOwnership( { caller : AnotherCaller } )
      =>
         throw
    ...</k>
    <tokenOwner> Caller </tokenOwner>
    <proposedOwner> _ => ProposedOwner </proposedOwner>
requires Caller =/=Int 0
    andBool ProposedOwner =/=Int 0
    andBool AnotherCaller =/=Int 0
    andBool ProposedOwner =/=Int AnotherCaller

// owner can change supply manager
rule
    <k>
        changeSupplyManager(SupplyManager, { caller : Caller } )
      => 
        .
    ...</k>
    <tokenOwner> Caller </tokenOwner>
    <supplyManager> _ => SupplyManager </supplyManager>
requires Caller =/=Int 0
    andBool SupplyManager =/=Int 0

// non-owner cannot change supply manager
rule
    <k>
        changeSupplyManager(_:Int, { caller : Caller } )
      =>
        throw
    ...</k>
    <tokenOwner> TokenOwner </tokenOwner>
requires TokenOwner =/=Int Caller

// owner can change asset protection manager
rule
    <k>
        changeAssetProtectionManager(AssetProtectionManager, { caller : Caller } )
      => 
        .
    ...</k>
    <tokenOwner> Caller </tokenOwner>
    <assetProtectionManager> _ => AssetProtectionManager </assetProtectionManager>
requires Caller =/=Int 0
    andBool AssetProtectionManager =/=Int 0

// non-owner cannot change asset protection manager
rule
    <k>
        changeAssetProtectionManager(_:Int, { caller : Caller } )
      =>
        throw
    ...</k>
    <tokenOwner> TokenOwner </tokenOwner>
requires TokenOwner =/=Int Caller

endmodule