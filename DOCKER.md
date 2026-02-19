# Docker Deployment Guide

**zkEVM Circuit Formal Verification Framework**

---

## 🐳 Why Docker?

- **One-click setup**: No manual Lean4 installation
- **Reproducible**: Same environment everywhere
- **Easy for reviewers**: EF can test in minutes
- **Cross-platform**: Works on Linux, macOS, Windows
- **Isolated**: No conflicts with system packages

---

## 📦 Quick Start (3 commands)

### Option 1: Automated (Recommended)

```bash
# Make script executable
chmod +x docker-quickstart.sh

# Run quick start (builds + tests)
./docker-quickstart.sh

# Run full demo
docker-compose run --rm zkevm-verifier ./docker-demo.sh
```

**Time**: 5-10 minutes (first build), < 30 seconds (subsequent runs)

---

### Option 2: Manual

```bash
# 1. Build image
docker-compose build

# 2. Run tests
docker-compose run --rm test

# 3. Run demo
docker-compose run --rm zkevm-verifier ./docker-demo.sh
```

---

## 🚀 Common Commands

### Interactive Shell

```bash
# Start bash shell in container
docker-compose run --rm zkevm-verifier bash

# Inside container:
$ python3 -c "from circuits import poseidon; print(poseidon.poseidon_circuit)"
$ cat proofs/Poseidon.lean
$ lean --version
```

### Run Specific Circuit

```bash
# Load Poseidon circuit
docker-compose run --rm zkevm-verifier \
  python3 -c "from circuits import poseidon; print(poseidon.poseidon_circuit)"

# Load ECC circuit
docker-compose run --rm zkevm-verifier \
  python3 -c "from circuits import ecc_add; print(ecc_add.ecc_add_circuit)"
```

### View Proofs and Reports

```bash
# View Poseidon proof
docker-compose run --rm zkevm-verifier cat proofs/Poseidon.lean

# View Poseidon report
docker-compose run --rm zkevm-verifier cat reports/Poseidon_report.md

# List all proofs
docker-compose run --rm zkevm-verifier ls -lh proofs/

# List all reports
docker-compose run --rm zkevm-verifier ls -lh reports/
```

---

## 📂 Volume Mounts

The `docker-compose.yml` mounts local directories:

| Local Path | Container Path | Purpose |
|------------|----------------|---------|
| `./circuits` | `/app/circuits` | Circuit definitions |
| `./src` | `/app/src` | Framework code |
| `./proofs` | `/app/proofs` | Lean4 proofs (read-only) |
| `./reports` | `/app/reports` | Verification reports |
| `./output` | `/app/output` | Generated files |

**Benefit**: Changes to local files are reflected in container immediately (useful for development).

---

## 🔧 Development Workflow

### Modify a Circuit

```bash
# 1. Edit circuit locally
nano circuits/poseidon.py

# 2. Test in container (no rebuild needed!)
docker-compose run --rm zkevm-verifier \
  python3 -c "from circuits import poseidon; print(poseidon.poseidon_circuit)"
```

### Add New Circuit

```bash
# 1. Create circuit file
cat > circuits/my_circuit.py << 'EOF'
from src.circuit import Circuit

my_circuit = Circuit(
    name="my_circuit",
    description="My custom circuit",
    inputs=["x: Field"],
    outputs=["y: Field"],
    constraints=["y = x * 2"]
)
EOF

# 2. Test immediately
docker-compose run --rm zkevm-verifier \
  python3 -c "from circuits import my_circuit; print(my_circuit.my_circuit)"
```

---

## 🏗️ Image Details

### Base Image

- **OS**: Ubuntu 22.04
- **Python**: 3.10+
- **Lean4**: Latest stable (via elan)

### Image Size

- **Built image**: ~800 MB
- **Compressed**: ~300 MB
- **Optimization**: Multi-stage build removes build tools

### Build Time

- **First build**: 5-10 minutes (downloads Lean4)
- **Rebuilds**: 1-2 minutes (cached layers)
- **With cache**: < 30 seconds

---

## 🎯 For EF Reviewers

### Test the Prototype (< 5 minutes)

```bash
# 1. Clone repository
git clone <repo-url>
cd zkevm-verifier-prototype

# 2. Run quick start
./docker-quickstart.sh

# 3. View demo
docker-compose run --rm zkevm-verifier ./docker-demo.sh
```

**Expected output**:
```
✅ All 5 circuits loaded successfully!
🔥 Poseidon Hash (Polygon zkEVM)
🔥 ECC Point Addition (ECRECOVER)
✅ Demo completed successfully! 🎉
```

### Interactive Exploration

```bash
# Start shell
docker-compose run --rm zkevm-verifier bash

# Inside container:
$ python3 circuits/poseidon.py    # Run circuit directly
$ cat proofs/Poseidon.lean        # View proof
$ cat reports/Poseidon_report.md  # Read report
$ lean --version                  # Check Lean4
```

---

## 🐛 Troubleshooting

### Build Fails

**Problem**: `lean: command not found` during build

**Solution**: Increase Docker memory allocation
```bash
# macOS/Windows: Docker Desktop > Settings > Resources > Memory: 4GB+
```

---

### Container Won't Start

**Problem**: `Error: container already exists`

**Solution**: Clean up old containers
```bash
docker-compose down
docker-compose up
```

---

### Permission Denied

**Problem**: `./docker-quickstart.sh: Permission denied`

**Solution**: Make scripts executable
```bash
chmod +x docker-quickstart.sh docker-demo.sh
```

---

### Slow Performance

**Problem**: Commands take too long

**Solution**: 
1. Ensure Docker has enough resources (2GB RAM, 2 CPUs min)
2. Use `--rm` flag to auto-remove containers
3. Prune unused images: `docker system prune -a`

---

## 🔒 Security Notes

### Image Safety

- **Base**: Official Ubuntu 22.04 image
- **Tools**: Installed from official sources
- **Dependencies**: Pinned versions in `requirements.txt`
- **Scanning**: Run `docker scan zkevm-verifier:latest`

### Network Isolation

By default, containers have no external network access except for package installation during build.

### Secrets

**DO NOT** include secrets in the image:
- Use environment variables
- Mount secrets at runtime
- Use Docker secrets in production

---

## 📊 Resource Usage

### Typical Usage

| Metric | Value |
|--------|-------|
| CPU | 1-2 cores |
| RAM | 2-4 GB |
| Disk | 1 GB (image + volumes) |
| Network | 500 MB (initial download) |

### Limits (configured in docker-compose.yml)

| Resource | Limit | Reservation |
|----------|-------|-------------|
| CPU | 2.0 cores | 1.0 core |
| Memory | 4 GB | 2 GB |

**Adjust** in `docker-compose.yml` if needed:
```yaml
deploy:
  resources:
    limits:
      cpus: '4.0'      # Increase for faster verification
      memory: 8G       # Increase for large circuits
```

---

## 🚢 Production Deployment

### CI/CD Integration

#### GitHub Actions

```yaml
# .github/workflows/verify.yml
name: Verify Circuits
on: [push, pull_request]

jobs:
  verify:
    runs-on: ubuntu-latest
    steps:
      - uses: actions/checkout@v2
      
      - name: Build Docker image
        run: docker-compose build
      
      - name: Run tests
        run: docker-compose run --rm test
      
      - name: Run demo
        run: docker-compose run --rm zkevm-verifier ./docker-demo.sh
```

#### GitLab CI

```yaml
# .gitlab-ci.yml
stages:
  - build
  - test

build:
  stage: build
  script:
    - docker-compose build
  
test:
  stage: test
  script:
    - docker-compose run --rm test
```

---

## 📦 Publishing Image

### Docker Hub

```bash
# Build and tag
docker build -t username/zkevm-verifier:1.0.0 .
docker build -t username/zkevm-verifier:latest .

# Push
docker push username/zkevm-verifier:1.0.0
docker push username/zkevm-verifier:latest
```

### GitHub Container Registry

```bash
# Tag
docker tag zkevm-verifier:latest ghcr.io/username/zkevm-verifier:latest

# Login
echo $GITHUB_TOKEN | docker login ghcr.io -u username --password-stdin

# Push
docker push ghcr.io/username/zkevm-verifier:latest
```

---

## 🎓 Advanced Usage

### Custom Lean4 Version

Edit `Dockerfile`:
```dockerfile
# Replace stable with specific version
RUN curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | \
    sh -s -- -y --default-toolchain leanprover/lean4:v4.5.0
```

### Mount Additional Directories

Edit `docker-compose.yml`:
```yaml
volumes:
  - ./circuits:/app/circuits
  - ./my-proofs:/app/my-proofs  # Add custom mount
```

### Override Entrypoint

```bash
# Run custom command
docker-compose run --rm --entrypoint python3 zkevm-verifier -c "print('Hello')"
```

---

## 📚 Further Reading

- [Docker Documentation](https://docs.docker.com/)
- [Docker Compose Reference](https://docs.docker.com/compose/)
- [Lean4 Docker Images](https://github.com/leanprover/lean4-docker)
- [Multi-stage Builds](https://docs.docker.com/build/building/multi-stage/)

---

## 🤝 Contributing

To improve Docker setup:

1. Test on your platform (Linux/macOS/Windows)
2. Optimize Dockerfile (reduce image size)
3. Add useful docker-compose services
4. Document edge cases

---

## ✅ Verification Checklist

**Before submitting to EF**:

- [ ] `docker-compose build` succeeds
- [ ] `docker-compose run test` passes
- [ ] `./docker-demo.sh` runs successfully
- [ ] All 5 circuits load
- [ ] Proofs and reports accessible
- [ ] Works on clean machine (test on fresh VM)
- [ ] README includes Docker instructions
- [ ] Image size < 1 GB

---

**Docker deployment ready!** 🐳

*zkEVM Circuit Formal Verification Framework v1.0.0*
