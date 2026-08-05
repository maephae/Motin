"""
Comparison Workflow: Random Fields → Spherical Morph → Target Overlap → Difference Heatmap
Generates an animation with multiple phases:
1. Flat extreme fields appear.
2. Morph to spherical shapes and interact.
3. Fade to black.
4. Show smooth target sphere, move it left, bring in a comparison field from the right.
5. Overlap target and field, then display difference heatmap alongside.
"""

import numpy as np
import matplotlib.pyplot as plt
from matplotlib.animation import FuncAnimation, PillowWriter
from mpl_toolkits.mplot3d import Axes3D

# ------------------------------------------------------------
# Parameters
# ------------------------------------------------------------
num_fields = 4                # must be a perfect square
grid_size = 60                # resolution
base_radius = 3.0
morph_frames = 80
interact_frames = 60
fade_frames = 40
target_show_frames = 80
overlap_frames = 80
heatmap_frames = 60
total_frames = (morph_frames + interact_frames + fade_frames +
                target_show_frames + overlap_frames + heatmap_frames)
fps = 20

# ------------------------------------------------------------
# 1. Generate extreme fields (as before)
# ------------------------------------------------------------
def generate_extreme_field(size):
    x = np.linspace(-2.5, 2.5, size)
    y = np.linspace(-2.5, 2.5, size)
    X, Y = np.meshgrid(x, y)
    Z = np.zeros_like(X)

    # Many sharp peaks
    for _ in range(np.random.randint(20, 35)):
        x0 = 4.5 * np.random.rand() - 2.25
        y0 = 4.5 * np.random.rand() - 2.25
        amp = 3.0 * np.random.rand() + 1.0
        wid = 0.06 * np.random.rand() + 0.06
        Z += amp * np.exp(-((X - x0)**2 + (Y - y0)**2) / (2 * wid**2))

    # Deep troughs
    for _ in range(np.random.randint(8, 15)):
        x0 = 4.5 * np.random.rand() - 2.25
        y0 = 4.5 * np.random.rand() - 2.25
        amp = -(2.5 * np.random.rand() + 0.8)
        wid = 0.08 * np.random.rand() + 0.08
        Z += amp * np.exp(-((X - x0)**2 + (Y - y0)**2) / (2 * wid**2))

    # Broad undulations
    for _ in range(3):
        x0 = 4.5 * np.random.rand() - 2.25
        y0 = 4.5 * np.random.rand() - 2.25
        amp = 1.2 * np.random.rand() - 0.6
        wid = 1.2 * np.random.rand() + 0.8
        Z += amp * np.exp(-((X - x0)**2 + (Y - y0)**2) / (2 * wid**2))

    Z = Z / np.max(np.abs(Z)) * 2.5
    return X, Y, Z

fields = []
for _ in range(num_fields):
    X, Y, Z = generate_extreme_field(grid_size)
    color = np.random.rand(3) * 0.6 + 0.4
    fields.append({'X': X, 'Y': Y, 'Z': Z, 'color': color})

# ------------------------------------------------------------
# 2. Spherical coordinates for each field
# ------------------------------------------------------------
for f in fields:
    X, Y = f['X'], f['Y']
    theta = (X + 2.5) / 5.0 * 2 * np.pi
    phi   = (Y + 2.5) / 5.0 * np.pi
    R_sph = base_radius + f['Z'] * 1.5
    Xs = R_sph * np.sin(phi) * np.cos(theta)
    Ys = R_sph * np.sin(phi) * np.sin(theta)
    Zs = R_sph * np.cos(phi)
    f.update({'theta': theta, 'phi': phi, 'Xs': Xs, 'Ys': Ys, 'Zs': Zs})

# ------------------------------------------------------------
# 3. Flat grid arrangement
# ------------------------------------------------------------
grid_pos = [(-4.5, -4.5), (4.5, -4.5), (-4.5, 4.5), (4.5, 4.5)]
for i, f in enumerate(fields):
    f['flat_x'] = f['X'] + grid_pos[i][0]
    f['flat_y'] = f['Y'] + grid_pos[i][1]
    f['flat_z'] = f['Z']

# ------------------------------------------------------------
# 4. Target field (smooth, circular)
# ------------------------------------------------------------
# Define a smooth radial perturbation: a spherical harmonic-like pattern
# We'll use the same theta,phi grid from the first field (same shape)
theta_t = fields[0]['theta']
phi_t   = fields[0]['phi']
# A smooth bump at the "equator" and symmetric in phi
# Use sin(phi)*cos(theta) gives a nice dipole pattern
target_Z = 0.8 * np.sin(phi_t) * np.cos(theta_t)   # smooth variation
# Also add a slight central Gaussian to make it more "circular"
target_Z += 0.5 * np.exp(-((theta_t - np.pi)**2 + (phi_t - np.pi/2)**2) / (2*0.8**2))
target_Z = target_Z / np.max(np.abs(target_Z)) * 0.8   # scale to match field amplitudes

# Spherical coords for target
R_target = base_radius + target_Z
Xt = R_target * np.sin(phi_t) * np.cos(theta_t)
Yt = R_target * np.sin(phi_t) * np.sin(theta_t)
Zt = R_target * np.cos(phi_t)

# ------------------------------------------------------------
# 5. Compute difference between first field and target
# ------------------------------------------------------------
field1_Z = fields[0]['Z']   # same grid as target_Z (since theta,phi from same field)
diff_Z = field1_Z - target_Z   # radial perturbation difference
# Normalize for heatmap display
diff_norm = diff_Z / np.max(np.abs(diff_Z))

# ------------------------------------------------------------
# 6. Setup figure with 3D and heatmap axes
# ------------------------------------------------------------
fig = plt.figure(figsize=(10, 8), facecolor='black')
ax3d = fig.add_subplot(121, projection='3d', facecolor='black')
ax3d.set_proj_type('ortho')
ax3d.axis('off')
ax3d.set_xlim(-7, 7); ax3d.set_ylim(-7, 7); ax3d.set_zlim(-7, 7)
ax3d.view_init(elev=20, azim=45)

ax_heat = fig.add_subplot(122, facecolor='black')
ax_heat.axis('off')   # will be turned on later

# We'll store surface objects for each field, and target, etc.
# Pre-create surfaces with dummy data; we'll update them
# For fields (flat and spherical)
field_surfs = []
for f in fields:
    s = ax3d.plot_surface(f['flat_x'], f['flat_y'], f['flat_z'],
                          facecolor=f['color'], edgecolor='none',
                          alpha=0.0, antialiased=True, shade=True)
    field_surfs.append(s)

# Target surface (fixed: we just store the collection)
target_surf = ax3d.plot_surface(Xt, Yt, Zt,
                                facecolor='cyan', edgecolor='none',
                                alpha=0.0, antialiased=True, shade=True)

# Heatmap image (initially empty)
heat_im = ax_heat.imshow(np.zeros((grid_size, grid_size)), cmap='RdBu_r',
                         vmin=-1, vmax=1, aspect='auto', origin='lower')
ax_heat.axis('off')

# ------------------------------------------------------------
# 7. Animation update function
# ------------------------------------------------------------
def update(frame):
    # Determine phase
    phase = 0
    t = 0.0
    subframe = 0
    if frame < morph_frames:
        phase = 0   # morph from flat to sphere
        t = frame / morph_frames
        t = t * t * (3 - 2 * t)  # ease
    elif frame < morph_frames + interact_frames:
        phase = 1   # interaction (spherical, breathing/fading)
        t = 1.0
        subframe = frame - morph_frames
    elif frame < morph_frames + interact_frames + fade_frames:
        phase = 2   # fade to black
        t = 1.0
        subframe = frame - morph_frames - interact_frames
        fade_out = 1 - subframe / fade_frames
    elif frame < morph_frames + interact_frames + fade_frames + target_show_frames:
        phase = 3   # show target alone, then move left
        t = 1.0
        subframe = frame - morph_frames - interact_frames - fade_frames
        target_alpha = min(1, subframe / 20)  # fade in quickly
        # Move target left: x offset from 0 to -3
        offset_x = -3 * min(1, max(0, (subframe - 30) / 30))
    else:
        phase = 4   # overlap with comparison field + heatmap
        subframe = frame - morph_frames - interact_frames - fade_frames - target_show_frames
        if subframe < overlap_frames:
            # show overlap of target and field1
            target_alpha_val = 1.0
            offset_x = -3   # target stays left
            # field1 appears from right: offset from 4 to 0
            field1_offset_x = 4 * (1 - subframe / overlap_frames)
            field1_alpha = min(1, subframe / 20)
            heatmap_alpha = 0.0
            field1_visible = True
        else:
            # show heatmap alongside
            target_alpha_val = 1.0
            offset_x = -3
            field1_offset_x = 0
            field1_alpha = 1.0
            heatmap_alpha = min(1, (subframe - overlap_frames) / 20)
            field1_visible = True

    # Clear and redraw 3D axis for each frame to avoid artifacts
    ax3d.clear()
    ax3d.set_proj_type('ortho')
    ax3d.axis('off')
    ax3d.set_xlim(-7, 7); ax3d.set_ylim(-7, 7); ax3d.set_zlim(-7, 7)
    ax3d.view_init(elev=20 + 10*np.sin(frame*0.02), azim=45 + 30*np.sin(frame*0.015))

    # ---- Draw fields ----
    for i, f in enumerate(fields):
        # Interpolate coordinates
        X_flat, Y_flat, Z_flat = f['flat_x'], f['flat_y'], f['flat_z']
        X_sph, Y_sph, Z_sph = f['Xs'], f['Ys'], f['Zs']

        if phase == 0:
            # Morphing
            X_cur = (1 - t) * X_flat + t * X_sph
            Y_cur = (1 - t) * Y_flat + t * Y_sph
            Z_cur = (1 - t) * Z_flat + t * Z_sph
            alpha = 0.3 + 0.5 * t   # fade in during morph
            field1_visible = False
        elif phase == 1:
            # Spherical with breathing and fading
            phase_shift = 2 * np.pi * i / num_fields
            breathe = 1 + 0.12 * np.sin(subframe * 0.08 + phase_shift * 2)
            R_breath = (base_radius + f['Z'] * 1.5) * breathe
            X_cur = R_breath * np.sin(f['phi']) * np.cos(f['theta'])
            Y_cur = R_breath * np.sin(f['phi']) * np.sin(f['theta'])
            Z_cur = R_breath * np.cos(f['phi'])
            fade = 0.2 + 0.5 * (0.5 + 0.5 * np.cos(subframe * 0.06 + phase_shift))
            alpha = fade
            field1_visible = False
        elif phase == 2:
            # Fade out
            X_cur = f['Xs']; Y_cur = f['Ys']; Z_cur = f['Zs']
            alpha = 0.6 * fade_out
            field1_visible = False
        else:
            # After fade, fields invisible except field1 in phase 4
            X_cur = f['Xs']; Y_cur = f['Ys']; Z_cur = f['Zs']
            alpha = 0.0
            field1_visible = False
            if phase == 4 and i == 0:
                field1_visible = True

        # For phase 4, we only show field1 (i=0) with special offset
        if phase == 4 and i == 0 and field1_visible:
            if 'field1_offset_x' in locals():
                X_cur = X_cur + field1_offset_x
            alpha = field1_alpha if 'field1_alpha' in locals() else 1.0
            # Plot if alpha > 0.01
            if alpha > 0.01:
                ax3d.plot_surface(X_cur, Y_cur, Z_cur,
                                  facecolor=f['color'], edgecolor='none',
                                  alpha=alpha, antialiased=True, shade=True,
                                  rstride=2, cstride=2)
        elif phase == 4 and i == 0:
            # Just in case
            pass
        elif phase < 3:
            # Plot if alpha > 0.01
            if alpha > 0.01:
                ax3d.plot_surface(X_cur, Y_cur, Z_cur,
                                  facecolor=f['color'], edgecolor='none',
                                  alpha=alpha, antialiased=True, shade=True,
                                  rstride=2, cstride=2)

    # ---- Draw target ----
    target_alpha_cur = 0.0
    target_offset_x = 0.0
    if phase == 3:
        target_alpha_cur = target_alpha if 'target_alpha' in locals() else 0
        target_offset_x = offset_x if 'offset_x' in locals() else 0
    elif phase == 4:
        target_alpha_cur = target_alpha_val if 'target_alpha_val' in locals() else 1
        target_offset_x = offset_x if 'offset_x' in locals() else -3
    else:
        target_alpha_cur = 0.0

    if target_alpha_cur > 0.01:
        Xt_off = Xt + target_offset_x
        Yt_off = Yt
        Zt_off = Zt
        ax3d.plot_surface(Xt_off, Yt_off, Zt_off,
                          facecolor='cyan', edgecolor='none',
                          alpha=target_alpha_cur, antialiased=True, shade=True,
                          rstride=2, cstride=2)

    # ---- Heatmap ----
    # Show only in phase 4 after overlap_frames
    if phase == 4 and subframe >= overlap_frames:
        # Display heatmap
        ax_heat.clear()
        ax_heat.imshow(diff_norm, cmap='RdBu_r', vmin=-1, vmax=1, aspect='auto', origin='lower')
        ax_heat.set_title('Radial Difference\n(Field1 - Target)', color='white', fontsize=10)
        ax_heat.axis('off')
    else:
        ax_heat.clear()
        ax_heat.axis('off')

    # Optional: add labels during target phase
    if phase == 3 and target_alpha_cur > 0.5:
        ax3d.text2D(0.05, 0.95, "Target Field (Smooth)", color='white', transform=ax3d.transAxes, fontsize=12)
    if phase == 4 and target_alpha_cur > 0.5:
        ax3d.text2D(0.05, 0.95, "Target vs. Field1", color='white', transform=ax3d.transAxes, fontsize=12)

    # Progress indicator
    if frame % 20 == 0:
        print(f"  Frame {frame+1}/{total_frames}", end='\r')
    
    return []

# ------------------------------------------------------------
# 8. Create animation
# ------------------------------------------------------------
print("Generating animation frames...")
anim = FuncAnimation(fig, update, frames=total_frames, interval=1000/fps, blit=False)

print("Saving as 'comparison.gif'...")
writer = PillowWriter(fps=fps)
anim.save('comparison.gif', writer=writer, dpi=100)
plt.close(fig)

print("\n✅ Done! Saved comparison.gif")
print("The animation shows:\n"
      "  - Phase 1: flat extreme fields appear and morph to spheres.\n"
      "  - Phase 2: spheres interact with breathing/fading.\n"
      "  - Phase 3: fade to black.\n"
      "  - Phase 4: smooth target appears, moves left; field1 appears from right.\n"
      "  - Phase 5: overlap target & field1, then difference heatmap appears.")