use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec::pairing::Pairing;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::rand::Rng;
use ark_std::UniformRand;

// TODO: prepare the G2 points
// Public protocol parameters, deducible from the max signers' set size and the trapdoor
struct GlobalSetup<C: Pairing> {
    domain: Radix2EvaluationDomain<C::ScalarField>,
    g1: C::G1Affine, // G1 generator
    g2: C::G2Affine, // G2 generator
    tau_g2: C::G2Affine, // tau.G2
    z_tau_g2: C::G2Affine, // Z(tau).G2, where Z(X)=X^n-1
    lis_g1: Vec<C::G1Affine>, // L_i(tau).G1
    lis_g2: Vec<C::G2Affine>, // L_i(tau).G2
}

#[derive(Clone)]
struct SignerPk<C: Pairing> {
    i: usize,
    pk_g1: C::G1,
    pk_g2: C::G2,
    c_g1: C::G1,
    // c_g2: C::G2,
    r_g1: C::G1,
}

struct Signer<C: Pairing> {
    sk: C::ScalarField,
    pk: SignerPk<C>,
    hints: Vec<C::G1>,
}

struct Aggregator<C: Pairing> {
    lis_g2: Vec<C::G2Affine>, // L_i(tau).G2
    hints_agg: Vec<C::G1>,
}

// Verifies aggregated signatures
struct Verifier<C: Pairing> {
    /// Committee public key.
    // Ct = sum(sk_i.L_i(tau)).G1),
    // over the set of signers, whose shares got verified and aggregated.
    ct: C::G1,
    g1: C::G1Affine, // G1 generator
    g2: C::G2Affine, // G2 generator
    tau_g2: C::G2Affine, // tau.G2
    z_tau_g2: C::G2Affine, // Z(tau).G2, where Z(X)=X^n-1
}

// Usual BLS signature, with the public key of the signer
struct BlsSigWithPk<C: Pairing> {
    sig: C::G1,
    pk: SignerPk<C>,
}

// Aggregate BLS signature together with
// - the corresponding BLS aggregate public keys (both in G1 and G2),
// - bitmask indicating the signers, committed to G2
// - other proof elements
struct Aggregated<C: Pairing> {
    asig_g1: C::G1, // BLS aggregate signature in G1
    apk_g1: C::G1, // BLS aggregate public key in G1
    apk_g2: C::G2, // BLS aggregate public key in G2
    b_g2: C::G2,
    cs: C::G1, // Lagrangian agg pk, sum of signers'
    q0: C::G1,
    cw: C::G1,
}

impl<C: Pairing> GlobalSetup<C> {
    fn setup<R: Rng>(log_n: usize, rng: &mut R) -> Self {
        let n = 1 << log_n;

        let g1 = C::G1Affine::generator();
        let g2 = C::G2Affine::generator();

        let tau = C::ScalarField::rand(rng);
        let tau_g2 = (g2 * tau).into_affine();
        let z_tau_g2 = (g2 * (tau.pow(&[n]) - C::ScalarField::one())).into_affine();

        let domain = Radix2EvaluationDomain::new(n as usize).unwrap();
        let lis_at_tau = domain.evaluate_all_lagrange_coefficients(tau);
        let lis_g1 = single_base_msm(&lis_at_tau, g1.into_group());
        let lis_g2 = single_base_msm(&lis_at_tau, g2.into_group());

        Self {
            domain,
            g1,
            g2,
            tau_g2,
            z_tau_g2,
            lis_g1,
            lis_g2,
        }
    }

    fn signer<R: Rng>(&self, i: usize, rng: &mut R) -> Signer<C> {
        let n = self.domain.size();
        let w = self.domain.group_gen;
        let sk = C::ScalarField::rand(rng);
        let pk_g1 = self.g1 * sk;
        let pk_g2 = self.g2 * sk;
        let nsk = self.domain.size_as_field_element * sk;
        let c_g1 = self.lis_g1[i] * nsk;
        // let c_g2 = self.lis_g2[i] * nsk;

        let mut wi_inv = C::ScalarField::one();

        let r_coeffs: Vec<_> = (0..n).map(|_| {
            let c = sk * wi_inv;
            wi_inv = wi_inv * self.domain.group_gen_inv;
            -c
        }).collect();
        let r_g1 = C::G1::msm(&self.lis_g1, &r_coeffs).unwrap();
        let r_g1 = r_g1 + c_g1 * w.pow(&[self.domain.size - i as u64]);

        let mut hints = vec![C::G1::zero(); n];
        let wi = w.pow(&[i as u64]);
        let mut wj = C::ScalarField::one();
        for j in 0..n {
            if j == i {
                wj = wj * w;
                continue;
            }
            let c = sk * (wi - wj).inverse().unwrap();
            let a = wj * c;
            let b = wi * c;
            hints[j] = self.lis_g1[i] * a - self.lis_g1[j] * b;
            wj = wj * w;
        }
        let hint_i = -hints.iter().sum::<C::G1>();
        hints[i] = hint_i;

        let pk = SignerPk {
            i,
            pk_g1,
            pk_g2,
            c_g1,
            // c_g2,
            r_g1,
        };

        Signer {
            sk,
            pk,
            hints,
        }
    }

    fn aggregator(&self, blocks: &[Vec<C::G1>]) -> Aggregator<C> {
        let n = self.domain.size();
        let hints_agg: Vec<_> = (0..n).map(|j| {
            blocks.iter()
                .map(|hints_i| hints_i[j])
                .sum::<C::G1>()
        }).collect();
        Aggregator {
            lis_g2: self.lis_g2.clone(),
            hints_agg,
        }
    }

    fn verifier(&self, ct: C::G1) -> Verifier<C> {
        Verifier {
            ct,
            g1: self.g1,
            g2: self.g2,
            tau_g2: self.tau_g2,
            z_tau_g2: self.z_tau_g2,
        }
    }

    // TODO: batch the pairings
    fn verify_pk(&self, pk: &SignerPk<C>) {
        // 1. PoPs
        // TODO
        // 2. DLEQ between the BLS keys in G1 and G2
        assert_eq!(
            C::pairing(pk.pk_g1, self.g2),
            C::pairing(self.g1, pk.pk_g2)
        );
        // 3. c_g1 well-formedness
        assert_eq!(
            C::pairing(pk.c_g1, self.g2),
            C::pairing(self.lis_g1[pk.i] * self.domain.size_as_field_element, pk.pk_g2)
        );
        // 4. r_g1 well-formedness
        assert_eq!(
            C::pairing(pk.c_g1 - pk.pk_g1, self.g2),
            C::pairing(pk.r_g1, self.tau_g2)
        );
    }
}

impl<C: Pairing> Signer<C> {
    fn sign(&self, message: C::G1) -> BlsSigWithPk<C> {
        BlsSigWithPk {
            sig: message * self.sk,
            pk: self.pk.clone(),
        }
    }
}

impl<C: Pairing> Aggregator<C> {
    fn aggregate(&self, sigs: &[BlsSigWithPk<C>]) -> Aggregated<C> {
        let asig_g1 = sigs.iter().map(|s| s.sig).sum();
        let apk_g1 = sigs.iter().map(|s| s.pk.pk_g1).sum();
        let apk_g2 = sigs.iter().map(|s| s.pk.pk_g2).sum();
        let cs = sigs.iter().map(|s| s.pk.c_g1).sum();
        let q0 = sigs.iter().map(|s| s.pk.r_g1).sum();
        let b_g2 = sigs.iter().map(|s| self.lis_g2[s.pk.i]).sum();
        let cw = sigs.iter().map(|s| self.hints_agg[s.pk.i]).sum();
        Aggregated {
            asig_g1,
            apk_g1,
            apk_g2,
            b_g2,
            cs,
            q0,
            cw,
        }
    }
}

// TODO: batch the pairings
impl<C: Pairing> Verifier<C> {
    fn verify(&self, sig: &Aggregated<C>, message: C::G1) {
        assert_eq!(
            C::pairing(self.ct, sig.b_g2),
            C::pairing(sig.cs, self.g2) + C::pairing(sig.cw, self.z_tau_g2)
        );
        // KZG verification of s(0) = apk
        assert_eq!(
            C::pairing(sig.cs - sig.apk_g1, self.g2),
            C::pairing(sig.q0, self.tau_g2)
        );
        // BLS signature verification, for the keys in G2
        assert_eq!(
            C::pairing(sig.asig_g1, self.g2),
            C::pairing(message, sig.apk_g2)
        );
        // DLEQ proof between APKs in G1 and G2
        assert_eq!(
            C::pairing(sig.apk_g1, self.g2),
            C::pairing(self.g1, sig.apk_g2)
        );
        // TODO: the degree check
    }
}


// Multiply the same base by each scalar.
pub fn single_base_msm<C: CurveGroup>(scalars: &[C::ScalarField], g: C) -> Vec<C::Affine> {
    let window_size = FixedBase::get_mul_window_size(scalars.len());
    let bits_in_scalar = C::ScalarField::MODULUS_BIT_SIZE.try_into().unwrap();
    let table = FixedBase::get_window_table(bits_in_scalar, window_size, g);
    let scalars_in_g = FixedBase::msm(bits_in_scalar, window_size, &table, scalars);
    C::normalize_batch(&scalars_in_g)
}

#[cfg(test)]
mod tests {
    use ark_bls12_381::{Bls12_381, G1Projective};
    use ark_std::{test_rng, UniformRand};

    use super::*;

    #[test]
    fn it_works() {
        let rng = &mut test_rng();

        let log_n = 2;
        let setup = GlobalSetup::<Bls12_381>::setup(log_n, rng);
        let n = setup.domain.size();

        let signers: Vec<_> = (0..n)
            .map(|i| setup.signer(i, rng))
            .collect();

        signers.iter().for_each(|s| setup.verify_pk(&s.pk));

        // Let's assume that all the hints arrived...
        let block: Vec<_> = signers.iter()
            .map(|s| s.hints.clone())
            .collect();
        let aggregator = setup.aggregator(&block);

        let c_agg_g1 = signers.iter()
            .map(|s| s.pk.c_g1)
            .sum::<G1Projective>(); // Committee pk

        let verifier = setup.verifier(c_agg_g1);

        let message = G1Projective::rand(rng);
        let sig0 = signers[0].sign(message);
        let sig2 = signers[2].sign(message);

        let agg_sig = aggregator.aggregate(&[sig0, sig2]);

        verifier.verify(&agg_sig, message);
    }
}
