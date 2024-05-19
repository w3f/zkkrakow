use subxt_signer::sr25519::{Keypair};
use avail_subxt::{
	avail::{Cells, Rows, TxInBlock, TxProgress},
	primitives::Cell,
	rpc::KateRpcClient as _,
	submit::submit_data_with_nonce,
	tx, AvailClient, Opts, AccountId,
};
use avail_core::AppId;
use  avail_subxt::utils::H256;
use avail_subxt::api::data_availability::calls::types::SubmitData;
const TURING_AVAILABILITY_NETWORK: &str  = "wss://turing-rpc.avail.so/ws"; 

pub struct AvailabilityBackend {
    availablity_network: String,
    availablity_provider_account: Keypair,
    provider_account_id : AccountId,
    client: AvailClient,
    
}


impl AvailabilityBackend {
    pub async fn initialize(availablity_mnemonic: String) -> AvailabilityBackend {
	let phrase = bip39::Mnemonic::parse(availablity_mnemonic).expect("valid phrase expected");

	let provider_account = Keypair::from_phrase(&phrase, None).expect("should be valid");
	AvailabilityBackend {
	    availablity_network: TURING_AVAILABILITY_NETWORK.to_string(),
            availablity_provider_account: provider_account.clone(),
            provider_account_id: provider_account.public_key().to_account_id(),
	    client: AvailClient::new(TURING_AVAILABILITY_NETWORK).await.unwrap(),
	}
    }

    pub async fn submit_data(&self, data: Vec<u8>) -> H256 {
	let nonce = self.client.tx().account_nonce(&self.provider_account_id).await.unwrap();
	println!("Submitting data to network");
	let submit_tx = submit_data_with_nonce(
		    &self.client,
		    &self.availablity_provider_account,
		    data.as_slice(),
	    AppId(1),
	    nonce as u64,	).await.unwrap();

		println!("Waiting until data submitted is finalized");
		let in_block = tx::in_finalized(submit_tx).await.unwrap();

		let hash = in_block.block_hash();
	println!("Submitted data in blocks: {hash:?}");
	hash

    }

    pub async fn retrieve_data(&self, block_hash: H256) -> Vec<u8> {
	let extrinsics = self.client.blocks().at(block_hash).await.unwrap().extrinsics().await.unwrap();
	let submit_call = extrinsics.find::<SubmitData>().next().unwrap().unwrap();
        //print!("data {:?}", submit_call.value.data);

	submit_call.value.data.0

    }

    
}

#[cfg(test)]
mod tests {
    use super::*;

    async fn  test_submit_to_avail() {
	let test_availablity_net = AvailabilityBackend::initialize("worth apart cage head yard argue usage guilt cigar sting flag dance".to_string());
	let block_hash = test_availablity_net.await.submit_data("Thu shalt remember us!".into()).await;
	println!("block hash: {}", block_hash);
    }
    #[tokio::test]
    async fn test_connection_to_avilability_network() {
	let test_availablity_net = AvailabilityBackend::initialize("worth apart cage head yard argue usage guilt cigar sting flag dance".to_string()).await;
	println!("provider id: {}", test_availablity_net.provider_account_id);
	
    }

    //#[tokio::test]
    async fn test_submit_to_avail_works() {
	test_submit_to_avail().await;
    }

    #[tokio::test]
    async fn retrieving_available_data_works() {
	let test_availablity_net = AvailabilityBackend::initialize("worth apart cage head yard argue usage guilt cigar sting flag dance".to_string()).await;
	let block_hash : [u8; 32] = array_bytes::hex2bytes_unchecked("43a01cce887163530ccf6904d46bae9afa795caff947e37a19558e71a1fba3e2").try_into().unwrap();
	let block_hash = H256::from(block_hash);
	let data = test_availablity_net.retrieve_data(block_hash).await;
         print!("data length {}", data.len());
         print!("data: {:x?}", data.as_slice());

    }
	    

}
