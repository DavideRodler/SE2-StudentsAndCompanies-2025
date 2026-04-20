# Students&Companies (S&C) Platform

> Software Engineering 2 Project — A.Y. 2024/2025, Politecnico di Milano

A platform designed to connect university students with companies offering internships. Students can search for opportunities, receive personalized recommendations, and manage applications, while companies can advertise positions, evaluate candidates, and schedule interviews.

## Authors

| Name | Contact |
|------|---------|
| **Davide Rodler** | [GitHub](https://github.com/DavideRodler) |
| **Stefano Riva** | |

## Project Documents

| Document | Description | PDF |
|----------|-------------|-----|
| **RASD** | Requirements Analysis & Specification Document | [`RASDv1.pdf`](DeliveryFolder/RASDv1.pdf) |
| **DD** | Design Document | [`DDv1.pdf`](DeliveryFolder/DDv1.pdf) |

## Repository Structure

```
├── RASD/                    # RASD LaTeX source
│   ├── RASD.tex
│   ├── rasd_diagrams/       # Use case, class, and state diagrams
│   ├── sequence_diagrams/   # Sequence diagrams
│   ├── alloy/               # Alloy model and analysis
│   └── project.als          # Alloy source file
├── DD/                      # DD LaTeX source
│   ├── DD.tex
│   ├── dd_diagrams/         # Component and deployment diagrams
│   ├── dd_sequence_diagram/ # DD sequence diagrams
│   └── dd_implementationImages/
└── DeliveryFolder/          # Final compiled PDFs
    ├── RASDv1.pdf
    └── DDv1.pdf
```

## Key Diagrams

### RASD
- **Use Case Diagram** — actors, system boundaries, and use case relationships
- **Class Diagram** — domain model of the S&C platform
- **State Diagrams** — internship and interview lifecycle
- **Alloy Model** — formal verification of system constraints

### DD
- **High-Level Architecture** — system overview
- **Component Diagram** — internal component structure and interfaces
- **Deployment Diagram** — infrastructure and deployment topology
- **Sequence Diagrams** — runtime interaction flows

## Tools & Technologies

- **LaTeX** — document typesetting
- **Alloy Analyzer** — formal modeling and verification
- **UML** — system modeling (use case, class, sequence, state, component, deployment)

## License

This project was developed for the Software Engineering 2 course at Politecnico di Milano.
