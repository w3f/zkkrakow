use crate::{GlobalSetup, availablity::AvailabilityBackend, Signer};
use ark_ec::pairing::Pairing;
use ark_std::rand::Rng;
use  avail_subxt::utils::H256;
use ark_serialize::{CanonicalSerialize, CanonicalDeserialize};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};

const PUB_KEY_SERIALIZED_SIZE : usize = 368; //(+ (* 3 48) (* 2 96) 32)
const CLUE_SERIALIZED_SIZE : usize = 48;

struct ClueAvailablifier {
    avail_backend: AvailabilityBackend
	
    
}
impl ClueAvailablifier {
    async fn initialize(availablity_mnemonic: String) -> ClueAvailablifier {
	ClueAvailablifier {
	    avail_backend: AvailabilityBackend::initialize(availablity_mnemonic).await,
	}
    }

    async fn make_available_signer<C: Pairing,R: Rng>(&self, setup: GlobalSetup<C>, i: usize, rng: &mut R) -> (Signer<C>, H256) {
	let mut all_pub_serialized: Vec<u8> = vec![0; PUB_KEY_SERIALIZED_SIZE];
	let s = setup.signer(i, rng);
	let all_clues = s.hints.iter().map(|s| {
	    let mut serialized_clue : Vec<u8> = vec![0; CLUE_SERIALIZED_SIZE];
	    s.serialize_compressed(&mut serialized_clue);
	    serialized_clue
	}
	).flatten().collect::<Vec<u8>>();
	s.pk.serialize_compressed(&mut all_pub_serialized[..]);
	let all_data = [all_pub_serialized, all_clues].concat();
	let block_hash = self.avail_backend.submit_data(all_data).await;
	(s, block_hash)
    }

}

#[cfg(test)]
mod tests {
    use super::*;
    use ark_bls12_381::{Bls12_381, G1Projective};
    use ark_std::{test_rng, UniformRand};

#[tokio::test]
async fn make_available_signers_work ()
{
        let rng = &mut test_rng();

        let log_n = 2;
    let setup = GlobalSetup::<Bls12_381>::setup(log_n, rng);
    
    let n = setup.domain.size();

    let clue_availer = ClueAvailablifier::initialize("worth apart cage head yard argue usage guilt cigar sting flag dance".to_string()).await;

    let available_signer = clue_availer.make_available_signer(setup, 0, rng).await;
    println!("signer {} is available at {:x?}", 0, available_signer.1);

}
}
