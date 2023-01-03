// SPDX-License-Identifier: MIT
pragma solidity ^0.8.4;

import "@openzeppelin/contracts/token/ERC721/extensions/ERC721URIStorage.sol";
import "@openzeppelin/contracts/token/ERC721/ERC721.sol";
import "@openzeppelin/contracts/utils/Counters.sol";
import "@openzeppelin/contracts/access/Ownable.sol";
import "../interfaces/IERC5192.sol";

contract ERC5192 is IERC5192, ERC721, ERC721URIStorage, Ownable {
  using Counters for Counters.Counter;
  Counters.Counter private _tokenIdCounter;

  error NotTokenOwnerAndNotContractOwner();
  error NonTransferableToken();

  mapping (uint256 => address) internal _tokenCreator;
  mapping (uint256 => bool) public lockedTokens;

  constructor(string memory _tokenName, string memory _tokenSymbol, bool _owner) ERC721(_tokenName, _tokenSymbol) {
    _transferOwnership(tx.origin);
    if(!_owner) renounceOwnership();
  }

  function safeMint(address to, string memory uri) public payable returns(uint256) {
    uint256 tokenId = _tokenIdCounter.current();
    _safeMint(to, tokenId);
    _setTokenURI(tokenId, uri);
    _tokenCreator[tokenId] = msg.sender;
    _tokenIdCounter.increment();
    return tokenId;
  }

  function lockMint(address to, string memory uri) public payable returns(uint256) {
    onlyContractOwnerIfExists();
    uint256 tokenId = safeMint(to, uri);
    lockToken(tokenId);
    emit Locked(tokenId);
    return tokenId;
  }

  function lockToken(uint256 tokenId) public {
    onlyTokenOwnerOrContractOwner(tokenId);   
    lockedTokens[tokenId] = true;
    emit Locked(tokenId);
  }

  function unlockToken(uint256 tokenId) private {
    lockedTokens[tokenId] = false;
    emit Unlocked(tokenId);
  }

  function locked(uint256 tokenId) 
    external 
    view 
    override(IERC5192) 
    returns (bool) 
  {
    return lockedTokens[tokenId];
  }

  function tokenURI(uint256 tokenId)
    public
    view
    override(ERC721, ERC721URIStorage)
    returns (string memory)
  {
    return super.tokenURI(tokenId);
  }

  function burn(uint256 tokenId) public {
    onlyTokenOwnerOrContractOwner(tokenId); 
    _burn(tokenId);
  }


  function onlyTokenOwnerOrContractOwner(uint256 tokenId) view internal {
    if(owner() != address(0)) {
      require(owner() == msg.sender, "sender is not the owner of the contract");
    } else {
      require(ownerOf(tokenId) == msg.sender, "sender is not the owner of the token");
    }
  }

  function onlyContractOwnerIfExists() view internal {
    if (owner() != address(0)) {
     _checkOwner();
    }
  }

  function _beforeTokenTransfer(address from, address to, uint256 tokenId, uint256 batchSize) 
    internal
    virtual 
    override(ERC721)
  {
    if (lockedTokens[tokenId] == true) {
      revert NonTransferableToken();
    }
    super._beforeTokenTransfer(from, to, tokenId, batchSize);
  }

  function _burn(uint256 tokenId) internal override(ERC721, ERC721URIStorage) {
    unlockToken(tokenId);
    super._burn(tokenId);
  }
}