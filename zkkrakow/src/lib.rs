use ark_ec::{AffineRepr, CurveGroup, VariableBaseMSM};
use ark_ec::pairing::Pairing;
use ark_ec::scalar_mul::fixed_base::FixedBase;
use ark_ff::{Field, One, PrimeField, Zero};
use ark_poly::{EvaluationDomain, Radix2EvaluationDomain};
use ark_std::{test_rng, UniformRand};

// TODO: prepare thew points
struct GlobalSetup<C: Pairing> {
    /// Maximal number of signers.
    // n: C::ScalarField,
    domain: Radix2EvaluationDomain<C::ScalarField>,
    g1: C::G1Affine,
    g2: C::G2Affine,
    tau_g2: C::G2Affine,
    z_tau_g2: C::G2Affine, //Z(tau).G2, where Z(X)=X^n-1
    lis_g1: Vec<C::G1Affine>,
    lis_g2: Vec<C::G2Affine>,
}

impl<C: Pairing> GlobalSetup<C> {
    fn setup(log_n: usize) -> Self { //todo: rng
        let g1 = C::G1Affine::generator();
        let g2 = C::G2Affine::generator();

        let tau = C::ScalarField::rand(&mut test_rng());
        let tau_g2 = (g2 * tau).into_affine();
        let n = 1 << log_n;
        let z_tau_g2 = (g2 * (tau.pow(&[n]) - C::ScalarField::one())).into_affine();

        let domain = Radix2EvaluationDomain::new(n as usize).unwrap();
        let lis_at_tau = domain.evaluate_all_lagrange_coefficients(tau);
        let lis_g1 = single_base_msm(&lis_at_tau, g1.into_group()); // L_i(tau).G1
        let lis_g2 = single_base_msm(&lis_at_tau, g2.into_group()); // L_i(tau).G2

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
}

struct Signer<C: Pairing> {
    i: usize,
    sk: C::ScalarField,
    pk_g1: C::G1, // todo: affine
    pk_g2: C::G2, // todo: affine
    c_g1: C::G1,
    c_g2: C::G2,
    r_g1: C::G1,
    hints: Vec<C::G1>,
}

impl<C: Pairing> GlobalSetup<C> {
    fn signer(&self, i: usize) -> Signer<C> { //TODO
        let n = self.domain.size();
        let w = self.domain.group_gen;
        let sk = C::ScalarField::rand(&mut test_rng());
        let pk_g1 = self.g1 * sk;
        let pk_g2 = self.g2 * sk;
        let nsk = self.domain.size_as_field_element * sk;
        let c_g1 = self.lis_g1[i] * nsk;
        let c_g2 = self.lis_g2[i] * nsk;

        let mut wi_inv = C::ScalarField::one();

        let r_coeffs: Vec<_> = (0..n).map(|_| {
            let z = sk * wi_inv;
            wi_inv = wi_inv * self.domain.group_gen_inv;
            -z
        }).collect();
        let r = C::G1::msm(&self.lis_g1, &r_coeffs).unwrap();

        let r_g1 = r + c_g1 * w.pow(&[self.domain.size - i as u64]);

        let mut hints = vec![C::G1::zero(); n];
        let wi = w.pow(&[i as u64]);
        let mut wj = C::ScalarField::one();
        for j in 0..n {
            if j == i {
                wj = wj * w;
                continue;
            }
            assert!(i != j, "i = {}, j = {}", i, j);
            assert!(wi != wj, "i = {}, j = {}", i, j);
            let denom = (self.domain.size_as_field_element * (wi - wj)).inverse().unwrap();
            let a = wj * denom;
            let b = wi * denom;
            hints[j] = self.lis_g1[i] * a + self.lis_g1[i] * b;
            wj = wj * w;
        }
        let hint_i = -hints.iter().sum::<C::G1>();
        hints[i] = hint_i;


        Signer {
            i,
            sk,
            pk_g1,
            pk_g2,
            c_g1,
            c_g2,
            r_g1,
            hints,
        }
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
    use super::*;
    use ark_bls12_381::{Bls12_381, G1Affine, G1Projective};

    #[test]
    fn it_works() {
        let log_n = 2;
        let setup = GlobalSetup::<Bls12_381>::setup(log_n);
        let n = setup.domain.size();
        assert_eq!(1 << log_n, n);
        let signers: Vec<_> = (0..n)
            .map(|i| setup.signer(i))
            .collect();

        let signer = &signers[1];
        assert_eq!(
            Bls12_381::pairing(signer.c_g1 - signer.pk_g1, setup.g2),
            Bls12_381::pairing(signer.r_g1, setup.tau_g2)
        );


        // let's assume that all the hints arrived
        let c_agg_g1 = signers.iter().map(|s| s.c_g1).sum::<G1Projective>(); // comittee pk

        let hints_agg: Vec<_> = (0..n).map(|j| {
            signers.iter()
                .map(|signer_i| signer_i.hints[j])
                .sum::<G1Projective>()
        }).collect();

        let message = G1Affine::rand(&mut test_rng());
        let sig0 = message * &signers[0].sk;
        let sig2 = message * &signers[2].sk;
        let apk = signers[0].pk_g1 + signers[2].pk_g1;

        let cs = &signers[0].c_g1 + &signers[2].c_g1;
        let b_g2 = setup.lis_g2[0] + setup.lis_g2[2];
        let cw = hints_agg[0] + hints_agg[2];

        assert_eq!(
            Bls12_381::pairing(c_agg_g1, b_g2),
            Bls12_381::pairing(cs, setup.g2) + Bls12_381::pairing(cw, setup.z_tau_g2)
        );

        let q0 = &signers[0].r_g1 + &signers[2].r_g1;

        assert_eq!(
            Bls12_381::pairing(cs - apk, setup.g2),
            Bls12_381::pairing(q0, setup.tau_g2)
        );
    }
}
