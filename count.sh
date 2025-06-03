#!/bin/sh

BACKWARD=core/properties/backward_traceability/*.v
FORWARD=core/properties/forward_traceability/*.v
CONFLUENCE=core/properties/confluence/*.v
ADDITIVITY=core/properties/additivity/*.v
UNIVERSALITY=core/properties/universality/*.v
INJECTIVITY=core/properties/injectivity/*.v
SURJECTIVITY=core/properties/surjectivity/*.v
L_INVERTIBILITY=core/properties/invertibility/*.v
R_INVERTIBILITY=core/properties/invertibility/*.v
MONOTONICITY=core/properties/monotonicity/*.v
DISTRIBUTIVITY=core/properties/distributivity/*.v

echo ""
coqwc $BACKWARD

echo ""
coqwc $FORWARD

echo ""
coqwc $CONFLUENCE

echo ""
coqwc $ADDITIVITY

echo ""
coqwc $UNIVERSALITY

echo ""
coqwc $INJECTIVITY

echo ""
coqwc $SURJECTIVITY

echo ""
coqwc $L_INVERTIBILITY

echo ""
coqwc $R_INVERTIBILITY

echo ""
coqwc $MONOTONICITY

echo ""
coqwc $DISTRIBUTIVITY

echo ""
echo "Properties Total"
coqwc $BACKWARD $FORWARD $CONFLUENCE $ADDITIVITY $UNIVERSALITY $INJECTIVITY $SURJECTIVITY $L_INVERTIBILITY $R_INVERTIBILITY $MONOTONICITY $DISTRIBUTIVITY

echo ""
echo "CoqTL Total"
coqwc core/*.v core/*/*.v core/*/*/*.v core/*/*/*/*.v usertools/*.v
