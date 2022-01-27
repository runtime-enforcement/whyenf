export const mockData = {
  formula: "(NOT a1) SINCE[4,8] a2",
  subformulas: ["(NOT a1)", "a2", "a1"],
  explanations: [
    {
      ts: 0,
      tp: 0,
      explanation: {
        type: "VSinceOutL",
        tp: 0,
        subexplanation: {},
        subexplanations: []
      }
    },
    {
      ts: 3,
      tp: 1,
      explanation: {
        type: "VSinceOutL",
        tp: 1,
        subexplanation: {},
        subexplanations: []
      }
    },
    {
      ts: 7,
      tp: 2,
      explanation: {
        type: "SSince",
        tp: 2,
        subexplanation: {
          type: "SAtom",
          tp: 1,
          atom: "a2"
        },
        subexplanations: [
          {
            type: "SNeg",
            tp: 2,
            subexplanation: {
              type: "VAtom",
              tp: 1,
              atom: "a1"
            },
            subexplanations: []
          }
        ]
      }
    },
    {
      ts: 11,
      tp: 3,
      explanation: {
        type: "VSince",
        tp: 3,
        subexplanation: {
          type: "VNeg",
          tp: 3,
          subexplanation: {
            type: "SAtom",
            tp: 3,
            atom: "a1"
          }
        },
        subexplanations: []
      }
    }
  ]
};
