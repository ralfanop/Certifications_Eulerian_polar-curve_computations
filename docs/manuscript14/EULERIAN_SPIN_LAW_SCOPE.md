# Finite-spin law: logarithmic saturation, endpoint duality, Fisher metric

For n=2J>0, levels J-k for k=0,...,n, Gibbs weights proportional to
exp((J-k)t), and r=exp(-t). The exact finite sums P=sum r^k and
A=sum(k r^(k-1), k=1,...,n) give J(1-q)=r A/P, with A(0)=P(0)=1.
This yields the logarithmic limit along the physical parameter t.
The uniform-reference log partition K=Jt+log P-log(n+1) has endpoint
convex conjugate sup_t(Jt-K)=log(n+1). Derivatives of actual Gibbs
moments imply K'=mean, mean'=variance; the finite Fisher metric is
the expectation of squared log-probability scores, equal to variance
and strictly positive for n>0. This is an analytic development of
the model in #727; it does not establish a physically generated
magnetic field. No manuscript files changed.

The first Lean module requests CI verification of 32 declarations.
Global inverse range, inverse endpoint limit as a function of q,
quantified remainder, classical endpoint divergence, and the metric
length to the endpoint remain subsequent targets. Do not infer their
formal certification from the present module.
