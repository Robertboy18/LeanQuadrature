/*
 * Polynomial replacement for cos in the quadrature example on [-1, 1].
 * This is an application-specific approximation, not a general libm cosine.
 * The Lean proof checks these decimal literals and every rounded operation.
 */
double cos(double x)
{
    x = x * x;
    return 1.0 + x * (-0.5 + x * (0.041666666666666664
        + x * (-0.001388888888888889
        + x * (0.00002480158730158730
        + x * (-0.0000002755731922398589
        + x * (0.000000002087675698786810
        + x * (-0.000000000011470745597729725 + x * 0.0)))))));
}
